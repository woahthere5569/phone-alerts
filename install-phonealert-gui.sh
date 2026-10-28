#!/usr/bin/env bash
# install-phonealert-gui.sh - Cisco phone alert server with web GUI, sounds and phone targeting
#
# Run on the Debian server:   sudo bash install-phonealert-gui.sh
# Safe to re-run / upgrade: keeps your passwords, phone list, sounds, ports and service settings.

set -euo pipefail

# ---------- settings (edit if anything changes) ----------
SERVER_IP="192.168.10.14"          # this Debian box
PORT=8080
PUSH_USER="alertpush"
DEFAULT_PHONES="1001=192.168.10.2,1002=192.168.10.3,1004=192.168.10.4,1003=192.168.10.12,1005=192.168.10.13"
LAN="192.168.10.0/24"
# ---------------------------------------------------------

CONFIG=/etc/phonealert.json
BIN=/usr/local/bin/phonealert.py
UI_DIR=/usr/local/share/phonealert
UNIT=/etc/systemd/system/phonealert.service

say()  { printf '\n\033[1;36m==> %s\033[0m\n' "$*"; }
warn() { printf '\033[1;33m!!  %s\033[0m\n' "$*"; }
ok()   { printf '\033[1;32mOK  %s\033[0m\n' "$*"; }

[[ $EUID -eq 0 ]] || { echo "Run this with sudo:  sudo bash $0"; exit 1; }

say "Checking prerequisites (python3, curl, ffmpeg)"
need=()
command -v python3 >/dev/null || need+=(python3)
command -v curl    >/dev/null || need+=(curl)
command -v ffmpeg  >/dev/null || need+=(ffmpeg)
if (( ${#need[@]} )); then
  echo "    installing: ${need[*]} (ffmpeg can take a few minutes)"
  apt-get update -qq
  DEBIAN_FRONTEND=noninteractive apt-get install -y -qq "${need[@]}" >/dev/null
fi
ok "$(python3 --version), curl, ffmpeg"

if ip -4 addr | grep -q "inet ${SERVER_IP}/"; then
  ok "this server has ${SERVER_IP}"
else
  warn "this server does NOT have ${SERVER_IP} - phones won't find it."
  warn "Its addresses are: $(ip -4 -o addr show scope global | awk '{print $4}' | xargs)"
  warn "Fix SERVER_IP at the top of this script (and CME's 'url authentication') if it changed."
fi

say "Installing program and web GUI"
mkdir -p "$UI_DIR"
cat > "$BIN" <<'PAPYEOF'
#!/usr/bin/env python3
"""
phonealert.py - pop-up + audio alerts for Cisco IP phones (CME, enterprise SIP firmware)

How it works
  * Text: the server pushes a CiscoIPPhoneExecute to each phone (/CGI/Execute).
    The phone checks the push with CME's "url authentication" (-> /auth here),
    then fetches /alert.xml and shows it on screen.
  * Audio: the same push tells the phone to open its speaker and receive an
    RTP stream (RTPRx URI). The server then streams the sound as G.711 u-law
    RTP to each phone and sends RTPRx:Stop when it's done.

Commands
  serve                              web GUI + phone endpoints (run by systemd)
  send "msg" -t TITLE [--phone IP]   send from the command line
       [--sound NAME] [--repeat N] [--volume 1-100]
  sounds                             list uploaded sounds
  add-sound FILE [--name NAME]       add a sound from the command line
  ports [main|audio|add|remove N]    show or change ports
  services [enable|disable NAME]     show or switch services on/off
  phones [add IP NAME|remove IP|rename IP NAME]   show or edit the phone list

Config: /etc/phonealert.json   Data: /var/lib/phonealert   Python 3 stdlib + ffmpeg
"""
import argparse
import base64
import hmac
import html
import json
import os
import random
import re
import shutil
import socket
import struct
import subprocess
import sys
import tempfile
import threading
import time
import urllib.error
import urllib.parse
import urllib.request
import uuid
from concurrent.futures import ThreadPoolExecutor
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

CONFIG_PATH = os.environ.get("PHONEALERT_CONFIG", "/etc/phonealert.json")
UI_PATH = os.environ.get("PHONEALERT_UI", "/usr/local/share/phonealert/index.html")

MAX_UPLOAD = 25 * 1024 * 1024      # bytes
MAX_SOUND_SECONDS = 120
MAX_REPEAT = 10
ULAW_SILENCE = b"\xff"

PHONE_ERRORS = {
    "1": "phone could not parse the request",
    "2": "phone could not build its response",
    "3": "phone internal file error",
    "4": "authentication failed (check CME 'url authentication' and credentials)",
}

_cfg_lock = threading.Lock()

# Services that can be switched off (web Settings panel or "phonealert.py services").
# Phone-facing endpoints (/auth, /alert.xml, /silence) are always on: pushes need them.
SERVICES = {
    "gui":           "Web control panel",
    "gui_login":     "Password on the web control panel",
    "audio":         "Sound alerts (audio on phone speakers)",
    "sound_uploads": "Uploading and deleting sounds from the web",
    "silence_key":   "Silence key on phone screens",
    "phone_editing": "Editing the phone list from the web",
    "history":       "Recording recent alerts",
    "web_settings":  "Changing ports and services from the web",
}


# ===================================================================== config

def load_config():
    with open(CONFIG_PATH) as f:
        cfg = json.load(f)
    for key in ("server_url", "push_user", "push_password", "phones"):
        if key not in cfg:
            sys.exit(f"config {CONFIG_PATH} is missing '{key}'")
    cfg.setdefault("listen_port", 8080)
    cfg.setdefault("data_dir", "/var/lib/phonealert")
    cfg.setdefault("admin_user", "admin")
    cfg.setdefault("admin_password", "")
    cfg.setdefault("rtp_port", 20480)
    # {phone_ip} {port} are filled in. Volume (":NN") is appended when chosen.
    cfg.setdefault("rtprx_uri", "RTPRx:{phone_ip}:{port}")
    cfg.setdefault("rtprx_stop_uri", "RTPRx:Stop")
    cfg.setdefault("extra_ports", [])
    cfg["listen_port"] = int(cfg["listen_port"])
    cfg["rtp_port"] = int(cfg["rtp_port"])
    cfg["extra_ports"] = sorted({int(p) for p in cfg["extra_ports"]} - {cfg["listen_port"]})
    svc = {k: True for k in SERVICES}
    for k, v in (cfg.get("services") or {}).items():
        if k in svc:
            svc[k] = bool(v)
    cfg["services"] = svc
    cfg["phones"] = [normalize_phone(p) for p in cfg["phones"]]
    for sub in ("alerts", "sounds", "tmp"):
        os.makedirs(os.path.join(cfg["data_dir"], sub), exist_ok=True)
    return cfg


def svc(cfg, name):
    return cfg["services"].get(name, True)


# ===================================================================== ports

def listen_ports(cfg):
    return [cfg["listen_port"]] + [p for p in cfg["extra_ports"] if p != cfg["listen_port"]]


def server_host(cfg):
    return urllib.parse.urlsplit(cfg["server_url"]).hostname


def port_free(port):
    s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
    try:
        s.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        s.bind(("0.0.0.0", port))
        return True
    except OSError:
        return False
    finally:
        s.close()


def check_ports(main, audio, extra, ours):
    """Validate a port plan. `ours` = ports this server already holds (skip the in-use test)."""
    def as_port(v, what):
        try:
            p = int(v)
        except (TypeError, ValueError):
            raise ValueError(f"{what} '{v}' is not a number")
        if not 1 <= p <= 65535:
            raise ValueError(f"{what} {p} must be between 1 and 65535")
        return p

    main = as_port(main, "web port")
    audio = as_port(audio, "audio port")
    if not 1024 <= audio <= 65534 or audio % 2:
        raise ValueError("audio port must be an even number between 1024 and 65534")
    clean = []
    for v in extra:
        p = as_port(v, "extra port")
        if p == main:
            raise ValueError(f"port {p} is already the main web port")
        if p in clean:
            raise ValueError(f"port {p} is listed twice")
        clean.append(p)
    if len(clean) > 10:
        raise ValueError("at most 10 extra ports")
    for p in [main] + clean:
        if p not in ours and not port_free(p):
            raise ValueError(f"port {p} is already used by another program on this server")
    return main, audio, sorted(clean)


def apply_ports(cfg, main, audio, extra):
    u = urllib.parse.urlsplit(cfg["server_url"])
    cfg["server_url"] = f"{u.scheme or 'http'}://{u.hostname}:{main}"
    cfg["listen_port"], cfg["rtp_port"], cfg["extra_ports"] = main, audio, extra


def ufw_allow(ports):
    """If ufw is on, open the web ports (best effort)."""
    if not shutil.which("ufw"):
        return
    try:
        st = subprocess.run(["ufw", "status"], capture_output=True, text=True, timeout=10).stdout
        if "Status: active" not in st:
            return
        for p in ports:
            subprocess.run(["ufw", "allow", f"{p}/tcp"], capture_output=True, timeout=10)
    except Exception:
        pass


def cme_note(cfg, old_main):
    """Text explaining the CME change needed when the main port moves."""
    if cfg["listen_port"] == old_main or old_main in cfg["extra_ports"]:
        return ""
    return ("The phones check pushes at the URL set in CME, which still uses port "
            f"{old_main}. Until you update CME, every alert will fail with error 4. On the ISR: "
            "conf t / voice register global / url authentication "
            f"http://{server_host(cfg)}:{cfg['listen_port']}/auth / create profile, then run "
            "tclsh flash:mkjabber.tcl and tclsh flash:webaccess.tcl and restart the phones. "
            f"(Or keep {old_main} as an extra port.)")


def restart_self(delay=0.8):
    """Re-exec this process so new ports take effect (works with or without systemd)."""
    def go():
        time.sleep(delay)
        sys.stdout.flush()
        sys.stderr.flush()
        os.execv(sys.executable, [sys.executable, os.path.abspath(sys.argv[0])] + sys.argv[1:])
    threading.Thread(target=go, daemon=True).start()


def restart_service():
    """After a CLI change: restart the running service, if any."""
    if shutil.which("systemctl"):
        r = subprocess.run(["systemctl", "is-active", "--quiet", "phonealert"],
                           capture_output=True)
        if r.returncode == 0:
            subprocess.run(["systemctl", "restart", "phonealert"])
            print("alert server restarted")
            return
    print("saved - restart the alert server to apply (sudo systemctl restart phonealert)")


def normalize_phone(p):
    if isinstance(p, str):
        return {"ip": p, "name": p}
    return {"ip": str(p["ip"]).strip(), "name": str(p.get("name") or p["ip"]).strip()}


def save_config(cfg):
    out = {k: v for k, v in cfg.items()}
    tmp = CONFIG_PATH + ".tmp"
    with open(tmp, "w") as f:
        json.dump(out, f, indent=2)
    os.chmod(tmp, 0o600)
    os.replace(tmp, CONFIG_PATH)


def write_json(path, data, mode=0o644):
    tmp = path + ".tmp"
    with open(tmp, "w") as f:
        json.dump(data, f, indent=2)
    os.chmod(tmp, mode)
    os.replace(tmp, path)


def read_json(path, default):
    try:
        with open(path) as f:
            return json.load(f)
    except (OSError, ValueError):
        return default


IP_RE = re.compile(r"^\d{1,3}(\.\d{1,3}){3}$")


def valid_ip(ip):
    return bool(IP_RE.match(ip)) and all(0 <= int(x) <= 255 for x in ip.split("."))


# ===================================================================== alerts

def alerts_dir(cfg):
    return os.path.join(cfg["data_dir"], "alerts")


def save_alert(cfg, title, text, has_sound):
    aid = uuid.uuid4().hex[:12]
    write_json(os.path.join(alerts_dir(cfg), aid + ".json"),
               {"id": aid, "title": title, "text": text, "has_sound": has_sound,
                "ts": int(time.time())})
    # keep the newest 100
    files = sorted((os.path.join(alerts_dir(cfg), n) for n in os.listdir(alerts_dir(cfg))
                    if n.endswith(".json")), key=os.path.getmtime)
    for old in files[:-100]:
        try:
            os.remove(old)
        except OSError:
            pass
    return aid


def load_alert(cfg, aid):
    if not aid or not re.fullmatch(r"[0-9a-f]{12}", aid):
        return None
    return read_json(os.path.join(alerts_dir(cfg), aid + ".json"), None)


def text_xml(cfg, alert):
    e = lambda s: html.escape(s, quote=True)
    if not alert:
        return ('<?xml version="1.0"?>\n<CiscoIPPhoneText><Title>Notice</Title>'
                "<Text>No active alert.</Text></CiscoIPPhoneText>")
    keys = ""
    pos = 1
    if alert.get("has_sound") and svc(cfg, "silence_key"):
        silence =f"{cfg['server_url'].rstrip('/')}/silence?id={alert['id']}"
        keys += (f"<SoftKeyItem><Name>Silence</Name><URL>{e(silence)}</URL>"
                 f"<Position>{pos}</Position></SoftKeyItem>")
        pos += 1
    keys += (f"<SoftKeyItem><Name>Dismiss</Name><URL>SoftKey:Exit</URL>"
             f"<Position>{pos}</Position></SoftKeyItem>")
    return ('<?xml version="1.0"?>\n<CiscoIPPhoneText>'
            f"<Title>{e(alert['title'][:32])}</Title>"
            f"<Text>{e(alert['text'][:4000])}</Text>{keys}</CiscoIPPhoneText>")


def history_path(cfg):
    return os.path.join(cfg["data_dir"], "history.json")


def add_history(cfg, entry):
    if not svc(cfg, "history"):
        return
    with _cfg_lock:
        h = read_json(history_path(cfg), [])
        h.insert(0, entry)
        write_json(history_path(cfg), h[:50])


# ===================================================================== sounds

def sounds_dir(cfg):
    return os.path.join(cfg["data_dir"], "sounds")


def sounds_index(cfg):
    return read_json(os.path.join(sounds_dir(cfg), "index.json"), [])


def save_sounds_index(cfg, idx):
    write_json(os.path.join(sounds_dir(cfg), "index.json"), idx)


def find_sound(cfg, key):
    if not key:
        return None
    for s in sounds_index(cfg):
        if s["id"] == key or s["name"].lower() == str(key).lower():
            return s
    return None


def add_sound(cfg, src_path, name):
    ff = shutil.which("ffmpeg")
    if not ff:
        raise RuntimeError("ffmpeg is not installed (sudo apt install ffmpeg)")
    name = (name or "sound").strip()[:60] or "sound"
    slug = re.sub(r"[^a-z0-9]+", "-", name.lower()).strip("-")[:40] or "sound"
    sid = f"{slug}-{uuid.uuid4().hex[:6]}"
    base = os.path.join(sounds_dir(cfg), sid)
    common = [ff, "-nostdin", "-hide_banner", "-loglevel", "error", "-y",
              "-i", src_path, "-t", str(MAX_SOUND_SECONDS), "-ac", "1", "-ar", "8000"]
    try:
        subprocess.run(common + ["-f", "mulaw", base + ".ulaw"],
                       check=True, capture_output=True, timeout=120)
        subprocess.run(common + ["-c:a", "pcm_s16le", base + ".wav"],
                       check=True, capture_output=True, timeout=120)
    except subprocess.CalledProcessError as e:
        for ext in (".ulaw", ".wav"):
            try:
                os.remove(base + ext)
            except OSError:
                pass
        msg = (e.stderr or b"").decode("utf-8", "replace").strip().splitlines()
        raise RuntimeError("could not read that audio file: " + (msg[-1] if msg else "ffmpeg failed"))
    size = os.path.getsize(base + ".ulaw")
    if size < 800:
        os.remove(base + ".ulaw")
        os.remove(base + ".wav")
        raise RuntimeError("that file has no usable audio")
    entry = {"id": sid, "name": name, "seconds": round(size / 8000, 1), "added": int(time.time())}
    with _cfg_lock:
        idx = sounds_index(cfg)
        idx.append(entry)
        save_sounds_index(cfg, idx)
    return entry


def delete_sound(cfg, sid):
    with _cfg_lock:
        idx = sounds_index(cfg)
        new = [s for s in idx if s["id"] != sid]
        if len(new) == len(idx):
            return False
        save_sounds_index(cfg, new)
    for ext in (".ulaw", ".wav"):
        try:
            os.remove(os.path.join(sounds_dir(cfg), sid + ext))
        except OSError:
            pass
    return True


def sound_bytes(cfg, sound):
    with open(os.path.join(sounds_dir(cfg), sound["id"] + ".ulaw"), "rb") as f:
        return f.read()


# ===================================================================== pushing

def execute(cfg, ip, urls, timeout=8):
    """Push up to 3 URLs to a phone. Returns (ok, message)."""
    items = "".join(f'<ExecuteItem Priority="0" URL="{html.escape(u, quote=True)}"/>'
                    for u in urls[:3])
    xml = f"<CiscoIPPhoneExecute>{items}</CiscoIPPhoneExecute>"
    body = ("XML=" + urllib.parse.quote_plus(xml)).encode()
    req = urllib.request.Request(f"http://{ip}/CGI/Execute", data=body, method="POST")
    token = base64.b64encode(f"{cfg['push_user']}:{cfg['push_password']}".encode()).decode()
    req.add_header("Authorization", "Basic " + token)
    req.add_header("Content-Type", "application/x-www-form-urlencoded")
    try:
        with urllib.request.urlopen(req, timeout=timeout) as r:
            resp = r.read().decode("utf-8", "replace")
    except urllib.error.HTTPError as e:
        return False, f"HTTP {e.code}"
    except Exception as e:  # timeout, refused (web access off?), unreachable
        reason = getattr(e, "reason", e)
        return False, str(reason)
    if "CiscoIPPhoneError" in resp:
        m = re.search(r'Number="(\d+)"', resp)
        n = m.group(1) if m else "?"
        return False, f"error {n}: {PHONE_ERRORS.get(n, 'unknown')}"
    bad = re.findall(r'Status="([1-9]\d*)"[^>]*?(?:Data="([^"]*)")?', resp)
    if bad:
        return False, "phone rejected part of the alert: " + ", ".join(
            (d or f"status {s}") for s, d in bad)
    return True, "ok"


def rtprx_uri(cfg, ip, volume):
    uri = cfg["rtprx_uri"].format(phone_ip=ip, port=cfg["rtp_port"])
    if volume:
        uri += f":{int(volume)}"
    return uri


# ===================================================================== RTP streaming

class Streamer:
    """One active audio stream at a time; a new alert replaces the old one."""

    def __init__(self):
        self.lock = threading.Lock()
        self.active = None  # dict(thread, stop, targets(set), info)

    def status(self):
        a = self.active
        if not a or not a["thread"].is_alive():
            return None
        return {"sound": a["info"]["sound"], "targets": sorted(a["targets"]),
                "started": a["info"]["started"], "seconds": a["info"]["seconds"]}

    def start(self, cfg, targets, ulaw, repeat, sound_name, block=False):
        with self.lock:
            self._stop_locked(keep=set(targets))
            stop = threading.Event()
            rec = {"stop": stop, "targets": set(targets),
                   "info": {"sound": sound_name, "started": int(time.time()),
                            "seconds": round(len(ulaw) * repeat / 8000, 1)}}
            t = threading.Thread(target=self._run, args=(cfg, rec, ulaw, repeat), daemon=True)
            rec["thread"] = t
            self.active = rec
            t.start()
        if block:
            try:
                while t.is_alive():
                    t.join(0.25)
            except KeyboardInterrupt:
                stop.set()
                t.join()

    def stop(self):
        with self.lock:
            return self._stop_locked(keep=set())

    def silence(self, ip):
        a = self.active
        if a and ip in a["targets"]:
            a["targets"].discard(ip)

    def _stop_locked(self, keep):
        a = self.active
        if not a or not a["thread"].is_alive():
            return False
        a["skip_stop"] = keep          # phones the next stream will reuse
        a["stop"].set()
        a["thread"].join(3)
        return True

    @staticmethod
    def _run(cfg, rec, ulaw, repeat):
        port = int(cfg["rtp_port"])
        gap = ULAW_SILENCE * 4000                       # 0.5 s between repeats
        pcm = (ulaw + gap) * (repeat - 1) + ulaw + ULAW_SILENCE * 1600
        if len(pcm) % 160:
            pcm += ULAW_SILENCE * (160 - len(pcm) % 160)
        seq = random.randint(0, 0xFFFF)
        ts = random.randint(0, 0xFFFFFFFF)
        ssrc = random.randint(1, 0xFFFFFFFF)
        sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        time.sleep(0.4)                                 # let phones open the speaker
        t0 = time.perf_counter()
        n = 0
        try:
            for off in range(0, len(pcm), 160):
                if rec["stop"].is_set():
                    break
                marker = 0x80 if n == 0 else 0
                pkt = struct.pack("!BBHII", 0x80, marker, seq, ts, ssrc) + pcm[off:off + 160]
                for ip in list(rec["targets"]):
                    try:
                        sock.sendto(pkt, (ip, port))
                    except OSError:
                        pass
                n += 1
                seq = (seq + 1) & 0xFFFF
                ts = (ts + 160) & 0xFFFFFFFF
                wait = t0 + n * 0.02 - time.perf_counter()
                if wait > 0:
                    rec["stop"].wait(wait)
        finally:
            sock.close()
            skip = rec.get("skip_stop", set())
            done = [ip for ip in rec["targets"] if ip not in skip]
            if done:
                with ThreadPoolExecutor(max_workers=min(16, len(done))) as ex:
                    list(ex.map(lambda ip: execute(cfg, ip, [cfg["rtprx_stop_uri"]], 5), done))


STREAMER = Streamer()


# ===================================================================== sending

def send_alert(cfg, title, text, targets, sound=None, repeat=1, volume=None,
               block_audio=False, source="cli"):
    title = (title or "ALERT").strip()[:32] or "ALERT"
    text = (text or "").strip()
    if sound and not svc(cfg, "audio"):
        raise ValueError("sound alerts are turned off (services enable audio)")
    if not text and not sound:
        raise ValueError("enter a message, choose a sound, or both")
    if not targets:
        raise ValueError("no phones selected")
    repeat = max(1, min(MAX_REPEAT, int(repeat or 1)))
    if volume not in (None, ""):
        volume = max(1, min(100, int(volume)))
    else:
        volume = None

    aid = save_alert(cfg, title, text, bool(sound)) if text else None
    alert_url = f"{cfg['server_url'].rstrip('/')}/alert.xml?id={aid}" if aid else None

    def one(ip):
        urls = []
        if alert_url:
            urls.append(alert_url)
        if sound:
            urls.append(rtprx_uri(cfg, ip, volume))
        ok, msg = execute(cfg, ip, urls)
        return ip, ok, msg

    with ThreadPoolExecutor(max_workers=min(16, len(targets))) as ex:
        results = list(ex.map(one, targets))

    names = {p["ip"]: p["name"] for p in cfg["phones"]}
    out = [{"ip": ip, "name": names.get(ip, ip), "ok": ok, "message": msg}
           for ip, ok, msg in results]
    accepted = [r["ip"] for r in out if r["ok"]]

    if sound and accepted:
        STREAMER.start(cfg, accepted, sound_bytes(cfg, sound), repeat, sound["name"],
                       block=block_audio)

    add_history(cfg, {"ts": int(time.time()), "title": title, "text": text,
                      "sound": sound["name"] if sound else None, "repeat": repeat,
                      "targets": [r["name"] for r in out], "ok": len(accepted),
                      "total": len(out), "source": source})
    return out


# ===================================================================== HTTP server

def make_handler(cfg):
    admin_token = base64.b64encode(
        f"{cfg['admin_user']}:{cfg['admin_password']}".encode()).decode()

    class Handler(BaseHTTPRequestHandler):
        server_version = "phonealert/2"

        def log_message(self, fmt, *args):
            if self.path.startswith(("/auth", "/alert.xml")):
                return
            sys.stderr.write("%s %s\n" % (self.address_string(), fmt % args))

        # ---- helpers
        def _send(self, code, body, ctype="text/plain; charset=utf-8", extra=None):
            data = body if isinstance(body, bytes) else body.encode("utf-8")
            self.send_response(code)
            self.send_header("Content-Type", ctype)
            self.send_header("Content-Length", str(len(data)))
            self.send_header("Cache-Control", "no-store")
            for k, v in (extra or {}).items():
                self.send_header(k, v)
            self.end_headers()
            if self.command != "HEAD":
                self.wfile.write(data)

        def _json(self, code, obj):
            self._send(code, json.dumps(obj), "application/json")

        def _admin_ok(self):
            if not svc(cfg, "gui"):
                self._send(404, "The web control panel is turned off.\n"
                                "Turn it back on with: sudo phonealert.py services enable gui\n")
                return False
            if not cfg["admin_password"] or not svc(cfg, "gui_login"):
                return True
            got = self.headers.get("Authorization", "")
            if got.startswith("Basic ") and hmac.compare_digest(got[6:].strip(), admin_token):
                return True
            self._send(401, "login required", extra={
                "WWW-Authenticate": 'Basic realm="Phone Alerts", charset="UTF-8"'})
            return False

        def _body(self, limit=1024 * 1024):
            n = int(self.headers.get("Content-Length") or 0)
            if n > limit:
                raise ValueError("request too large")
            return self.rfile.read(n) if n else b""

        def _query(self):
            u = urllib.parse.urlsplit(self.path)
            return u.path, {k.lower(): v[0] for k, v in urllib.parse.parse_qs(u.query).items()}

        # ---- GET
        def do_GET(self):
            path, q = self._query()

            # phone-facing (no admin login)
            if path == "/auth":
                ok = hmac.compare_digest(q.get("userid", ""), cfg["push_user"]) and \
                     hmac.compare_digest(q.get("password", ""), cfg["push_password"])
                return self._send(200, "AUTHORIZED" if ok else "UN-AUTHORIZED")
            if path == "/alert.xml":
                return self._send(200, text_xml(cfg, load_alert(cfg, q.get("id"))), "text/xml")
            if path == "/silence":
                ip = self.client_address[0]
                STREAMER.silence(ip)
                threading.Thread(target=execute, args=(cfg, ip, [cfg["rtprx_stop_uri"]], 5),
                                 daemon=True).start()
                alert = load_alert(cfg, q.get("id"))
                if alert:
                    alert = dict(alert, has_sound=False)
                return self._send(200, text_xml(cfg, alert), "text/xml")

            # admin
            if not self._admin_ok():
                return
            if path in ("/", "/index.html"):
                try:
                    with open(UI_PATH, "rb") as f:
                        return self._send(200, f.read(), "text/html; charset=utf-8")
                except OSError:
                    return self._send(500, f"UI file missing: {UI_PATH}")
            if path == "/api/state":
                return self._json(200, {
                    "phones": cfg["phones"],
                    "sounds": sounds_index(cfg) if svc(cfg, "audio") else [],
                    "history": read_json(history_path(cfg), [])[:20] if svc(cfg, "history") else [],
                    "streaming": STREAMER.status(),
                    "ffmpeg": bool(shutil.which("ffmpeg")),
                    "limits": {"repeat": MAX_REPEAT, "seconds": MAX_SOUND_SECONDS,
                               "upload_mb": MAX_UPLOAD // (1024 * 1024)},
                    "services": cfg["services"],
                    "service_info": SERVICES,
                    "ports": {"main": cfg["listen_port"], "audio": cfg["rtp_port"],
                              "extra": cfg["extra_ports"]},
                    "server_host": server_host(cfg),
                })
            m = re.fullmatch(r"/api/sounds/([a-z0-9-]+)\.wav", path)
            if m and svc(cfg, "audio"):
                p = os.path.join(sounds_dir(cfg), m.group(1) + ".wav")
                if os.path.isfile(p):
                    with open(p, "rb") as f:
                        return self._send(200, f.read(), "audio/wav")
            return self._send(404, "not found")

        do_HEAD = do_GET

        # ---- POST
        def do_POST(self):
            if not self._admin_ok():
                return
            path, q = self._query()
            try:
                if path == "/api/send":
                    d = json.loads(self._body() or b"{}")
                    sound = find_sound(cfg, d.get("sound")) if d.get("sound") else None
                    if d.get("sound") and not sound:
                        return self._json(400, {"error": "that sound no longer exists"})
                    known = {p["ip"] for p in cfg["phones"]}
                    targets = [ip for ip in d.get("phones", []) if ip in known]
                    res = send_alert(cfg, d.get("title"), d.get("text"), targets, sound,
                                     d.get("repeat", 1), d.get("volume"), source="web")
                    return self._json(200, {"results": res})
                if path == "/api/stop":
                    return self._json(200, {"stopped": STREAMER.stop()})
                if path == "/api/settings":
                    return self._settings(json.loads(self._body() or b"{}"))
                if path == "/api/phones":
                    if not svc(cfg, "phone_editing"):
                        return self._json(403, {"error": "editing phones from the web is turned off"})
                    d = json.loads(self._body() or b"[]")
                    phones, seen = [], set()
                    for p in d:
                        p = normalize_phone(p)
                        if not valid_ip(p["ip"]):
                            return self._json(400, {"error": f"'{p['ip']}' is not a valid IP"})
                        if p["ip"] in seen:
                            return self._json(400, {"error": f"{p['ip']} is listed twice"})
                        seen.add(p["ip"])
                        p["name"] = p["name"][:40] or p["ip"]
                        phones.append(p)
                    with _cfg_lock:
                        cfg["phones"] = phones
                        save_config(cfg)
                    return self._json(200, {"phones": phones})
                if path == "/api/sounds":
                    if not (svc(cfg, "audio") and svc(cfg, "sound_uploads")):
                        return self._json(403, {"error": "sound uploads are turned off"})
                    n = int(self.headers.get("Content-Length") or 0)
                    if n <= 0:
                        return self._json(400, {"error": "empty upload"})
                    if n > MAX_UPLOAD:
                        return self._json(413, {"error": f"file is over {MAX_UPLOAD // 1048576} MB"})
                    fd, tmp = tempfile.mkstemp(dir=os.path.join(cfg["data_dir"], "tmp"))
                    try:
                        with os.fdopen(fd, "wb") as f:
                            left = n
                            while left:
                                chunk = self.rfile.read(min(65536, left))
                                if not chunk:
                                    break
                                f.write(chunk)
                                left -= len(chunk)
                        entry = add_sound(cfg, tmp, q.get("name"))
                    finally:
                        try:
                            os.remove(tmp)
                        except OSError:
                            pass
                    return self._json(200, entry)
            except (ValueError, RuntimeError) as e:
                return self._json(400, {"error": str(e)})
            return self._send(404, "not found")

        # ---- settings (ports + services)
        def _settings(self, d):
            if not svc(cfg, "web_settings"):
                return self._json(403, {"error": "changing settings from the web is turned off"})
            ports = d.get("ports") or {}
            services = d.get("services") or {}
            unknown = [k for k in services if k not in SERVICES]
            if unknown:
                return self._json(400, {"error": "unknown service: " + ", ".join(unknown)})
            with _cfg_lock:
                old = (cfg["listen_port"], cfg["rtp_port"], list(cfg["extra_ports"]))
                ours = set(listen_ports(cfg))
                new = check_ports(ports.get("main", old[0]), ports.get("audio", old[1]),
                                  ports.get("extra", old[2]), ours)
                apply_ports(cfg, *new)
                for k, v in services.items():
                    cfg["services"][k] = bool(v)
                save_config(cfg)
                web_ports_changed = (old[0], sorted(old[2])) != (new[0], new[2])
            if web_ports_changed:
                ufw_allow(listen_ports(cfg))
                restart_self()
            return self._json(200, {
                "restarting": web_ports_changed,
                "ports": {"main": cfg["listen_port"], "audio": cfg["rtp_port"],
                          "extra": cfg["extra_ports"]},
                "services": cfg["services"],
                "note": cme_note(cfg, old[0]),
            })

        # ---- DELETE
        def do_DELETE(self):
            if not self._admin_ok():
                return
            if not (svc(cfg, "audio") and svc(cfg, "sound_uploads")):
                return self._json(403, {"error": "sound uploads are turned off"})
            path, _ = self._query()
            m = re.fullmatch(r"/api/sounds/([a-z0-9-]+)", path)
            if m and delete_sound(cfg, m.group(1)):
                return self._json(200, {"deleted": m.group(1)})
            return self._send(404, "not found")

    return Handler


def serve(cfg):
    handler = make_handler(cfg)
    servers = []
    for port in listen_ports(cfg):
        try:
            srv = ThreadingHTTPServer(("0.0.0.0", port), handler)
        except OSError as e:
            if port == cfg["listen_port"]:
                sys.exit(f"cannot listen on main port {port}: {e}")
            print(f"warning: skipping extra port {port}: {e}", flush=True)
            continue
        srv.daemon_threads = True
        servers.append(srv)
        threading.Thread(target=srv.serve_forever, daemon=True).start()
    ports = ", ".join(str(s.server_address[1]) for s in servers)
    off = [k for k, v in cfg["services"].items() if not v]
    print(f"phonealert listening on {ports}  (GUI: {cfg['server_url']}/)"
          + (f"  services off: {', '.join(off)}" if off else ""), flush=True)
    try:
        while True:
            time.sleep(3600)
    except KeyboardInterrupt:
        pass


# ===================================================================== CLI commands

def cmd_ports(cfg, action, port):
    if action == "show":
        print(f"main web port : {cfg['listen_port']}   (GUI, phone auth and alert pages)")
        print(f"extra ports   : {', '.join(map(str, cfg['extra_ports'])) or 'none'}   (also serve the GUI and phone pages)")
        print(f"audio port    : {cfg['rtp_port']}   (UDP port the phones receive sound on)")
        print(f"GUI address   : {cfg['server_url']}/")
        return
    if port is None:
        sys.exit(f"usage: phonealert.py ports {action} PORT")
    main, audio, extra = cfg["listen_port"], cfg["rtp_port"], list(cfg["extra_ports"])
    if action == "main":
        extra = [p for p in extra if p != port]
        main = port
    elif action == "audio":
        audio = port
    elif action == "add":
        if port in extra or port == main:
            sys.exit(f"port {port} is already in use by the alert server")
        extra.append(port)
    elif action == "remove":
        if port == main:
            sys.exit("that's the main port - change it with: ports main NEWPORT")
        if port not in extra:
            sys.exit(f"port {port} is not an extra port")
        extra.remove(port)
    old_main = cfg["listen_port"]
    try:
        new = check_ports(main, audio, extra, set(listen_ports(cfg)))
    except ValueError as e:
        sys.exit(str(e))
    apply_ports(cfg, *new)
    save_config(cfg)
    if action in ("main", "add"):
        ufw_allow(listen_ports(cfg))
    cmd_ports(cfg, "show", None)
    note = cme_note(cfg, old_main)
    if note:
        print("\nIMPORTANT: " + note)
    restart_service()


def cmd_services(cfg, action, name):
    if action == "show":
        for k, label in SERVICES.items():
            print(f"{'on ' if cfg['services'][k] else 'OFF'}  {k:<14} {label}")
        print("\nchange with: phonealert.py services enable|disable NAME")
        return
    if name not in SERVICES:
        sys.exit(f"unknown service '{name}'. Choose from: {', '.join(SERVICES)}")
    cfg["services"][name] = action == "enable"
    save_config(cfg)
    print(f"{name}: {'on' if action == 'enable' else 'OFF'}  ({SERVICES[name]})")
    restart_service()


def cmd_phones(cfg, action, args):
    phones = cfg["phones"]
    if action == "show":
        for ph in phones:
            print(f"{ph['ip']:<16} {ph['name']}")
        return
    if action == "add":
        if not args:
            sys.exit("usage: phonealert.py phones add IP [NAME]")
        ip, name = args[0], " ".join(args[1:]) or args[0]
        if not valid_ip(ip):
            sys.exit(f"'{ip}' is not a valid IP")
        if any(ph["ip"] == ip for ph in phones):
            sys.exit(f"{ip} is already in the list")
        phones.append({"ip": ip, "name": name[:40]})
    elif action == "remove":
        if not args or not any(ph["ip"] == args[0] for ph in phones):
            sys.exit("usage: phonealert.py phones remove IP   (IP must be in the list)")
        cfg["phones"] = [ph for ph in phones if ph["ip"] != args[0]]
    elif action == "rename":
        if len(args) < 2:
            sys.exit("usage: phonealert.py phones rename IP NEW NAME")
        for ph in phones:
            if ph["ip"] == args[0]:
                ph["name"] = " ".join(args[1:])[:40]
                break
        else:
            sys.exit(f"{args[0]} is not in the list")
    save_config(cfg)
    cmd_phones(cfg, "show", [])
    restart_service()


# ===================================================================== CLI

def main():
    p = argparse.ArgumentParser(description="Pop-up and audio alerts for Cisco IP phones")
    sub = p.add_subparsers(dest="cmd", required=True)
    sub.add_parser("serve", help="run the web GUI and phone endpoints")
    s = sub.add_parser("send", help="send an alert")
    s.add_argument("text", nargs="?", default="", help="message text")
    s.add_argument("-t", "--title", default="ALERT", help="title bar (max 32 chars)")
    s.add_argument("--phone", action="append", help="only this phone IP (repeatable)")
    s.add_argument("--sound", help="sound name or id to play")
    s.add_argument("--repeat", type=int, default=1, help=f"play the sound N times (max {MAX_REPEAT})")
    s.add_argument("--volume", type=int, help="speaker volume 1-100 (default: phone's own)")
    sub.add_parser("sounds", help="list sounds")
    a2 = sub.add_parser("add-sound", help="add a sound file")
    a2.add_argument("file")
    a2.add_argument("--name")
    pp = sub.add_parser("ports", help="show or change ports",
                        description="ports [show] | main PORT | audio PORT | add PORT | remove PORT")
    pp.add_argument("action", nargs="?", default="show",
                    choices=["show", "main", "audio", "add", "remove"])
    pp.add_argument("port", nargs="?", type=int)
    sp = sub.add_parser("services", help="show, enable or disable services",
                        description="services [show] | enable NAME | disable NAME.  Names: "
                                    + ", ".join(SERVICES))
    sp.add_argument("action", nargs="?", default="show", choices=["show", "enable", "disable"])
    sp.add_argument("name", nargs="?")
    php = sub.add_parser("phones", help="show or edit the phone list",
                         description="phones [show] | add IP [NAME] | remove IP | rename IP NAME")
    php.add_argument("action", nargs="?", default="show", choices=["show", "add", "remove", "rename"])
    php.add_argument("args", nargs="*")
    a = p.parse_args()

    cfg = load_config()
    if a.cmd == "serve":
        serve(cfg)
    elif a.cmd == "ports":
        cmd_ports(cfg, a.action, a.port)
    elif a.cmd == "services":
        cmd_services(cfg, a.action, a.name)
    elif a.cmd == "phones":
        cmd_phones(cfg, a.action, a.args)
    elif a.cmd == "sounds":
        for snd in sounds_index(cfg):
            print(f"{snd['name']:<30} {snd['seconds']:>6}s   id={snd['id']}")
    elif a.cmd == "add-sound":
        e = add_sound(cfg, a.file, a.name or os.path.splitext(os.path.basename(a.file))[0])
        print(f"added '{e['name']}' ({e['seconds']}s)")
    else:
        sound = None
        if a.sound:
            sound = find_sound(cfg, a.sound)
            if not sound:
                sys.exit(f"no sound called '{a.sound}' (see: phonealert.py sounds)")
        targets = a.phone or [ph["ip"] for ph in cfg["phones"]]
        try:
            res = send_alert(cfg, a.title, a.text, targets, sound, a.repeat, a.volume,
                             block_audio=True)
        except ValueError as e:
            sys.exit(str(e))
        failed = 0
        for r in res:
            print(f"{r['ip']:<16} {'OK  ' if r['ok'] else 'FAIL'} {r['name']}  {r['message'] if not r['ok'] else ''}")
            failed += not r["ok"]
        print(f"{len(res) - failed}/{len(res)} phones accepted the alert")
        sys.exit(1 if failed else 0)


if __name__ == "__main__":
    main()
PAPYEOF
cat > "$UI_DIR/index.html" <<'PAHTMLEOF'
<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Phone Alerts</title>
<style>
:root {
  --bg: #f4f2ee; --panel: #ffffff; --ink: #1d1c1a; --muted: #6b675f; --line: #e3dfd7;
  --accent: #b42318; --accent-ink: #ffffff; --accent-soft: #fde8e6;
  --ok: #1f7a4a; --ok-soft: #e3f3ea; --warn: #9a5b00; --warn-soft: #fdf1dc;
  --chip: #efece6; --focus: #2457c5; --shadow: 0 1px 2px rgba(0,0,0,.05), 0 4px 16px rgba(0,0,0,.04);
}
@media (prefers-color-scheme: dark) {
  :root {
    --bg: #161514; --panel: #201f1d; --ink: #f1eee8; --muted: #a39e94; --line: #34322e;
    --accent: #e5483b; --accent-ink: #ffffff; --accent-soft: #3a1d1a;
    --ok: #4fbf84; --ok-soft: #1a2e23; --warn: #e2a33d; --warn-soft: #33281a;
    --chip: #2b2a27; --focus: #7aa2ff; --shadow: none;
  }
}
* { box-sizing: border-box; }
body { margin: 0; background: var(--bg); color: var(--ink);
  font: 15px/1.45 ui-sans-serif, system-ui, -apple-system, "Segoe UI", Roboto, sans-serif; }
header { position: sticky; top: 0; z-index: 5; background: var(--bg);
  border-bottom: 1px solid var(--line); }
.bar { max-width: 1080px; margin: 0 auto; padding: 14px 16px; display: flex; align-items: center; gap: 12px; }
.bar h1 { font-size: 18px; margin: 0; letter-spacing: -.01em; }
.bar .dot { width: 10px; height: 10px; border-radius: 50%; background: var(--accent); }
.spacer { flex: 1; }
main { max-width: 1080px; margin: 0 auto; padding: 18px 16px 48px; display: grid; gap: 18px;
  grid-template-columns: minmax(0, 1.5fr) minmax(0, 1fr); align-items: start; }
@media (max-width: 860px) { main { grid-template-columns: minmax(0, 1fr); } }
section { background: var(--panel); border: 1px solid var(--line); border-radius: 12px;
  padding: 18px; box-shadow: var(--shadow); }
section h2 { font-size: 15px; margin: 0 0 14px; display: flex; align-items: center; gap: 8px; }
section h2 small { color: var(--muted); font-weight: 400; }
.stack { display: grid; gap: 18px; }
label { display: block; font-size: 13px; font-weight: 600; margin: 0 0 6px; }
.hint { color: var(--muted); font-size: 12.5px; font-weight: 400; }
input[type=text], input[type=number], textarea, select {
  width: 100%; padding: 9px 11px; border: 1px solid var(--line); border-radius: 8px;
  background: var(--bg); color: var(--ink); font: inherit; }
textarea { min-height: 96px; resize: vertical; }
input:focus, textarea:focus, select:focus, button:focus-visible { outline: 2px solid var(--focus); outline-offset: 1px; }
.row { display: grid; gap: 12px; grid-template-columns: repeat(auto-fit, minmax(140px, 1fr)); }
.field { margin-bottom: 14px; }
.count { float: right; color: var(--muted); font-weight: 400; font-size: 12px; }
button { font: inherit; border-radius: 8px; border: 1px solid var(--line); background: var(--panel);
  color: var(--ink); padding: 8px 13px; cursor: pointer; }
button:hover { border-color: var(--muted); }
button:disabled { opacity: .55; cursor: not-allowed; }
.primary { background: var(--accent); border-color: var(--accent); color: var(--accent-ink); font-weight: 600; }
.primary:hover { filter: brightness(1.06); border-color: var(--accent); }
.big { width: 100%; padding: 13px; font-size: 16px; }
.ghost { background: transparent; border-color: transparent; color: var(--muted); padding: 6px 8px; }
.ghost:hover { color: var(--ink); border-color: var(--line); }
.chips { display: flex; flex-wrap: wrap; gap: 8px; margin-bottom: 14px; }
.chip { background: var(--chip); border-color: transparent; border-radius: 999px; padding: 6px 12px; font-size: 13px; }
.phones { display: grid; gap: 6px; grid-template-columns: repeat(auto-fill, minmax(170px, 1fr)); }
.ph { display: flex; gap: 9px; align-items: center; padding: 9px 11px; border: 1px solid var(--line);
  border-radius: 8px; cursor: pointer; user-select: none; }
.ph:has(input:checked) { border-color: var(--accent); background: var(--accent-soft); }
.ph input { width: 16px; height: 16px; accent-color: var(--accent); margin: 0; }
.ph b { display: block; font-weight: 600; font-size: 14px; }
.ph span { color: var(--muted); font-size: 12px; font-variant-numeric: tabular-nums; }
.tools { display: flex; gap: 4px; margin-left: auto; }
.results { display: grid; gap: 6px; margin-top: 14px; }
.res { display: flex; gap: 10px; align-items: baseline; padding: 8px 11px; border-radius: 8px; font-size: 14px; }
.res.ok { background: var(--ok-soft); } .res.bad { background: var(--accent-soft); }
.res .tag { font-weight: 700; font-size: 12px; min-width: 34px; }
.res.ok .tag { color: var(--ok); } .res.bad .tag { color: var(--accent); }
.res .msg { color: var(--muted); font-size: 13px; }
.pill { display: inline-flex; align-items: center; gap: 8px; border-radius: 999px; padding: 5px 6px 5px 12px;
  background: var(--warn-soft); color: var(--warn); font-size: 13px; font-weight: 600; }
.pill button { padding: 4px 10px; font-size: 12.5px; }
.pulse { width: 8px; height: 8px; border-radius: 50%; background: currentColor; animation: p 1s infinite; }
@keyframes p { 50% { opacity: .25; } }
.list { display: grid; gap: 0; }
.item { display: flex; gap: 10px; align-items: center; padding: 10px 0; border-top: 1px solid var(--line); }
.item:first-child { border-top: 0; }
.item .grow { flex: 1; min-width: 0; }
.item .t { font-weight: 600; white-space: nowrap; overflow: hidden; text-overflow: ellipsis; }
.item .s { color: var(--muted); font-size: 12.5px; }
.empty { color: var(--muted); font-size: 13.5px; padding: 6px 0; }
.upl { display: grid; gap: 8px; grid-template-columns: 1fr; margin-top: 12px; padding-top: 12px; border-top: 1px dashed var(--line); }
.upl .r { display: flex; gap: 8px; }
.upl input[type=file] { font-size: 13px; color: var(--muted); max-width: 100%; }
.ptable { display: grid; gap: 8px; }
.prow { display: grid; grid-template-columns: 1fr 1fr auto; gap: 8px; }
.note { font-size: 13px; padding: 9px 11px; border-radius: 8px; background: var(--warn-soft); color: var(--warn); margin-bottom: 12px; }
.toast { position: fixed; left: 50%; bottom: 22px; transform: translateX(-50%); background: var(--ink); color: var(--bg);
  padding: 10px 16px; border-radius: 10px; font-size: 14px; opacity: 0; transition: opacity .2s; pointer-events: none; max-width: calc(100% - 32px); }
.toast.show { opacity: 1; }
.hist .t { font-weight: 600; }
.hist .s { white-space: normal; }
audio { display: none; }
.hidden { display: none !important; }
h3.sub { font-size: 12px; text-transform: uppercase; letter-spacing: .06em; color: var(--muted);
  margin: 18px 0 10px; font-weight: 700; }
h3.sub:first-child { margin-top: 0; }
.svc { display: flex; align-items: center; gap: 12px; padding: 9px 0; border-top: 1px solid var(--line); }
.svc:first-child { border-top: 0; }
.svc .grow { flex: 1; min-width: 0; }
.svc .t { font-size: 14px; }
.svc code { font-size: 11.5px; color: var(--muted); }
.tg { appearance: none; -webkit-appearance: none; width: 40px; height: 23px; border-radius: 999px; flex: none;
  background: var(--line); position: relative; cursor: pointer; transition: background .15s; margin: 0; }
.tg::after { content: ""; position: absolute; top: 3px; left: 3px; width: 17px; height: 17px; border-radius: 50%;
  background: #fff; box-shadow: 0 1px 2px rgba(0,0,0,.25); transition: left .15s; }
.tg:checked { background: var(--ok); }
.tg:checked::after { left: 20px; }
.tg:focus-visible { outline: 2px solid var(--focus); outline-offset: 2px; }
.ports { display: flex; flex-wrap: wrap; gap: 6px; margin: 8px 0; }
.port { display: inline-flex; align-items: center; gap: 4px; background: var(--chip); border-radius: 999px;
  padding: 4px 4px 4px 11px; font-size: 13px; font-variant-numeric: tabular-nums; }
.port button { border: 0; background: transparent; padding: 2px 7px; color: var(--muted); }
.port button:hover { color: var(--ink); }
.addrow { display: flex; gap: 8px; }
.addrow input { max-width: 140px; }
.banner { max-width: 1080px; margin: 14px auto 0; padding: 0 16px; }
.banner > div { padding: 12px 14px; border-radius: 10px; font-size: 14px; line-height: 1.5; }
.banner .info { background: var(--ok-soft); color: var(--ink); }
.banner .warn { background: var(--warn-soft); color: var(--ink); border-left: 4px solid var(--warn); }
.banner code, .note code { font-size: 12.5px; word-break: break-all; }
.off-chip { font-size: 12px; font-weight: 600; color: var(--warn); background: var(--warn-soft);
  border-radius: 999px; padding: 4px 10px; }
.foot { display: flex; align-items: center; gap: 10px; margin-top: 16px; }
</style>
</head>
<body>
<header>
  <div class="bar">
    <div class="dot"></div>
    <h1>Phone Alerts</h1>
    <div class="spacer"></div>
    <span id="loginOff" class="off-chip hidden">No login</span>
    <div id="streaming"></div>
  </div>
</header>
<div class="banner hidden" id="banner"></div>

<main>
  <div class="stack">
    <section>
      <h2>Send an alert</h2>
      <div class="chips" id="presets"></div>

      <div class="field">
        <label for="title">Title <span class="count" id="titleCount">0/32</span></label>
        <input type="text" id="title" maxlength="32" placeholder="EARTHQUAKE WARNING">
      </div>
      <div class="field">
        <label for="text">Message <span class="hint">(leave empty to only play a sound)</span></label>
        <textarea id="text" maxlength="4000" placeholder="Drop, cover and hold on. Stay away from windows."></textarea>
      </div>

      <div class="row field" id="soundRow">
        <div>
          <label for="sound">Sound</label>
          <select id="sound"></select>
        </div>
        <div>
          <label for="repeat">Play</label>
          <select id="repeat"></select>
        </div>
        <div>
          <label for="volume">Volume <span class="hint">1–100</span></label>
          <input type="number" id="volume" min="1" max="100" placeholder="phone's own">
        </div>
      </div>

      <div class="field">
        <label style="display:flex;align-items:center">Phones
          <span class="hint" id="selCount" style="margin-left:8px"></span>
          <span class="tools">
            <button class="ghost" id="selAll" type="button">All</button>
            <button class="ghost" id="selNone" type="button">None</button>
          </span>
        </label>
        <div class="phones" id="targets"></div>
      </div>

      <button class="primary big" id="send" type="button">Send alert</button>
      <div class="results" id="results"></div>
    </section>

    <section>
      <h2>Recent alerts</h2>
      <div class="list hist" id="history"></div>
    </section>
  </div>

  <div class="stack">
    <section>
      <h2>Sounds <small id="soundCount"></small></h2>
      <div id="ffmpegNote"></div>
      <div class="list" id="sounds"></div>
      <div class="upl" id="uploadArea">
        <label for="file" style="margin:0">Upload a sound <span class="hint">MP3, WAV, M4A… up to <span id="upMax">25</span> MB, first <span id="secMax">120</span> s used</span></label>
        <input type="file" id="file" accept="audio/*,.mp3,.wav,.m4a,.ogg,.flac,.aac">
        <div class="r">
          <input type="text" id="soundName" placeholder="Name, e.g. Siren" maxlength="60">
          <button id="upload" type="button">Upload</button>
        </div>
      </div>
    </section>

    <section>
      <h2>Phones</h2>
      <div id="phoneLock"></div>
      <div class="ptable" id="phoneEdit"></div>
      <div style="display:flex;gap:8px;margin-top:12px" id="phoneBtns">
        <button id="addPhone" type="button">Add phone</button>
        <div class="spacer"></div>
        <button class="primary" id="savePhones" type="button">Save</button>
      </div>
    </section>

    <section id="settingsSec">
      <h2>Settings</h2>
      <div id="settingsLock"></div>
      <div id="settingsBody">
        <h3 class="sub">Ports</h3>
        <div class="row field">
          <div>
            <label for="pMain">Main web port</label>
            <input type="number" id="pMain" min="1" max="65535">
          </div>
          <div>
            <label for="pAudio">Phone audio port</label>
            <input type="number" id="pAudio" min="1024" max="65534" step="2">
          </div>
        </div>
        <label>Extra web ports <span class="hint">the panel and phone pages also answer here</span></label>
        <div class="ports" id="pExtra"></div>
        <div class="addrow">
          <input type="number" id="pExtraNew" min="1" max="65535" placeholder="e.g. 8081" aria-label="Extra port to add">
          <button id="pExtraAdd" type="button">Add port</button>
        </div>

        <h3 class="sub">Services</h3>
        <div id="svcList"></div>

        <div class="foot">
          <span class="hint" id="settingsDirty"></span>
          <div class="spacer"></div>
          <button class="primary" id="saveSettings" type="button">Save settings</button>
        </div>
      </div>
    </section>
  </div>
</main>

<audio id="player"></audio>
<div class="toast" id="toast"></div>

<script>
const $ = (id) => document.getElementById(id);
const esc = (s) => String(s ?? "").replace(/[&<>"']/g, c => ({"&":"&amp;","<":"&lt;",">":"&gt;",'"':"&quot;","'":"&#39;"}[c]));
let state = { phones: [], sounds: [], history: [], streaming: null };
let selected = null;   // Set of IPs

const PRESETS = [
  ["Earthquake", "EARTHQUAKE WARNING", "Drop, cover and hold on. Stay away from windows until the shaking stops."],
  ["Fire", "FIRE - EVACUATE", "Leave the building now by the nearest exit. Do not use elevators."],
  ["Severe weather", "SEVERE WEATHER", "Move to an interior room on the lowest floor and stay away from windows."],
  ["All clear", "ALL CLEAR", "The emergency is over. You may resume normal activity."],
  ["Test", "TEST ALERT", "This is a test of the phone alert system. No action is needed."],
];

function toast(msg) {
  const t = $("toast"); t.textContent = msg; t.classList.add("show");
  clearTimeout(t._h); t._h = setTimeout(() => t.classList.remove("show"), 3200);
}

async function api(path, opts = {}) {
  const r = await fetch(path, opts);
  let body = null;
  try { body = await r.json(); } catch (_) {}
  if (!r.ok) throw new Error((body && body.error) || `${r.status} ${r.statusText}`);
  return body;
}

function ago(ts) {
  const s = Math.floor(Date.now() / 1000 - ts);
  if (s < 60) return "just now";
  if (s < 3600) return `${Math.floor(s / 60)} min ago`;
  if (s < 86400) return `${Math.floor(s / 3600)} h ago`;
  return new Date(ts * 1000).toLocaleString();
}

function renderPresets() {
  $("presets").innerHTML = PRESETS.map((p, i) => `<button class="chip" data-i="${i}" type="button">${esc(p[0])}</button>`).join("");
  $("presets").onclick = (e) => {
    const b = e.target.closest("button"); if (!b) return;
    const p = PRESETS[+b.dataset.i];
    $("title").value = p[1]; $("text").value = p[2]; updateCount();
  };
}

function updateCount() { $("titleCount").textContent = `${$("title").value.length}/32`; }

function renderTargets() {
  const ips = state.phones.map(p => p.ip);
  if (selected === null) selected = new Set(ips);
  for (const ip of [...selected]) if (!ips.includes(ip)) selected.delete(ip);
  $("targets").innerHTML = state.phones.length ? state.phones.map(p => `
    <label class="ph"><input type="checkbox" value="${esc(p.ip)}" ${selected.has(p.ip) ? "checked" : ""}>
      <div><b>${esc(p.name)}</b><span>${esc(p.ip)}</span></div></label>`).join("")
    : `<div class="empty">No phones yet. Add them in the Phones panel.</div>`;
  $("selCount").textContent = `${selected.size} of ${state.phones.length} selected`;
}
$("targets").addEventListener("change", (e) => {
  if (e.target.type !== "checkbox") return;
  e.target.checked ? selected.add(e.target.value) : selected.delete(e.target.value);
  $("selCount").textContent = `${selected.size} of ${state.phones.length} selected`;
});
$("selAll").onclick = () => { selected = new Set(state.phones.map(p => p.ip)); renderTargets(); };
$("selNone").onclick = () => { selected = new Set(); renderTargets(); };

function renderSoundSelect() {
  const cur = $("sound").value;
  $("sound").innerHTML = `<option value="">No sound</option>` +
    state.sounds.map(s => `<option value="${esc(s.id)}">${esc(s.name)} (${s.seconds}s)</option>`).join("");
  if (state.sounds.some(s => s.id === cur)) $("sound").value = cur;
}

function renderSounds() {
  $("soundCount").textContent = state.sounds.length ? `${state.sounds.length}` : "";
  $("sounds").innerHTML = state.sounds.length ? state.sounds.map(s => `
    <div class="item">
      <div class="grow"><div class="t">${esc(s.name)}</div><div class="s">${s.seconds} s</div></div>
      <button data-play="${esc(s.id)}" type="button">Preview</button>
      ${on("sound_uploads") ? `<button class="ghost" data-del="${esc(s.id)}" type="button" aria-label="Delete ${esc(s.name)}">Delete</button>` : ""}
    </div>`).join("") : `<div class="empty">${on("audio") ? (on("sound_uploads") ? "No sounds yet. Upload a siren or chime below." : "No sounds yet. Add one on the server with: sudo phonealert.py add-sound FILE") : "Sound alerts are turned off in Settings."}</div>`;
  renderSoundSelect();
}
$("sounds").addEventListener("click", async (e) => {
  const b = e.target.closest("button"); if (!b) return;
  if (b.dataset.play) {
    const pl = $("player");
    if (!pl.paused && pl.dataset.id === b.dataset.play) { pl.pause(); b.textContent = "Preview"; return; }
    document.querySelectorAll("[data-play]").forEach(x => x.textContent = "Preview");
    pl.src = `/api/sounds/${b.dataset.play}.wav`; pl.dataset.id = b.dataset.play;
    pl.onended = () => b.textContent = "Preview";
    try { await pl.play(); b.textContent = "Stop"; } catch (err) { toast("Could not play preview"); }
  }
  if (b.dataset.del) {
    const s = state.sounds.find(x => x.id === b.dataset.del);
    if (!confirm(`Delete "${s ? s.name : "this sound"}"?`)) return;
    try { await api(`/api/sounds/${b.dataset.del}`, { method: "DELETE" }); await refresh(); toast("Sound deleted"); }
    catch (err) { toast(err.message); }
  }
});

$("file").onchange = () => {
  const f = $("file").files[0];
  if (f && !$("soundName").value) $("soundName").value = f.name.replace(/\.[^.]+$/, "").slice(0, 60);
};
$("upload").onclick = async () => {
  const f = $("file").files[0];
  if (!f) return toast("Choose a file first");
  const name = $("soundName").value.trim() || f.name;
  $("upload").disabled = true; $("upload").textContent = "Converting…";
  try {
    const s = await api(`/api/sounds?name=${encodeURIComponent(name)}`, { method: "POST", body: f });
    $("file").value = ""; $("soundName").value = "";
    await refresh(); $("sound").value = s.id;
    toast(`Added "${s.name}" (${s.seconds}s)`);
  } catch (err) { toast(err.message); }
  finally { $("upload").disabled = false; $("upload").textContent = "Upload"; }
};

let phoneDraft = [];
function renderPhoneEdit() {
  const ro = !on("phone_editing");
  $("phoneLock").innerHTML = ro ? `<div class="note">Editing phones from the web is turned off. On the server: <code>sudo phonealert.py phones</code></div>` : "";
  $("phoneBtns").classList.toggle("hidden", ro);
  $("phoneEdit").innerHTML = phoneDraft.map((p, i) => `
    <div class="prow">
      <input type="text" data-i="${i}" data-k="name" value="${esc(p.name)}" placeholder="Name, e.g. 1001 Kitchen" aria-label="Phone name" ${ro ? "disabled" : ""}>
      <input type="text" data-i="${i}" data-k="ip" value="${esc(p.ip)}" placeholder="192.168.10.x" inputmode="decimal" aria-label="Phone IP" ${ro ? "disabled" : ""}>
      ${ro ? "<span></span>" : `<button class="ghost" data-rm="${i}" type="button" aria-label="Remove">✕</button>`}
    </div>`).join("") || `<div class="empty">No phones.</div>`;
}

// ---------- services + settings
const on = (k) => !state.services || state.services[k] !== false;

function applyServices() {
  $("soundRow").classList.toggle("hidden", !on("audio"));
  $("uploadArea").classList.toggle("hidden", !(on("audio") && on("sound_uploads")));
  $("loginOff").classList.toggle("hidden", on("gui_login"));
  if (!on("audio")) $("sound").value = "";
}

function banner(html, kind = "info") {
  $("banner").innerHTML = html ? `<div class="${kind}">${html}</div>` : "";
  $("banner").classList.toggle("hidden", !html);
}

let settingsDraft = null;
function loadSettingsDraft() {
  settingsDraft = { main: state.ports.main, audio: state.ports.audio, extra: [...state.ports.extra],
                    services: { ...state.services } };
}
function settingsChanged() {
  const s = settingsDraft, p = state.ports;
  return s.main !== p.main || s.audio !== p.audio || s.extra.join() !== p.extra.join() ||
    Object.keys(s.services).some(k => s.services[k] !== state.services[k]);
}
function markDirty() { $("settingsDirty").textContent = settingsChanged() ? "Unsaved changes" : ""; }

function renderSettings() {
  const locked = !on("web_settings");
  $("settingsLock").innerHTML = locked ? `<div class="note">Settings are locked. Unlock on the server with: <code>sudo phonealert.py services enable web_settings</code></div>` : "";
  $("settingsBody").classList.toggle("hidden", locked);
  if (locked) return;
  $("pMain").value = settingsDraft.main;
  $("pAudio").value = settingsDraft.audio;
  $("pExtra").innerHTML = settingsDraft.extra.length ? settingsDraft.extra.map(p =>
    `<span class="port">${p}<button type="button" data-rmport="${p}" aria-label="Remove port ${p}">✕</button></span>`).join("")
    : `<span class="hint">None</span>`;
  $("svcList").innerHTML = Object.entries(state.service_info).map(([k, label]) => `
    <label class="svc"><div class="grow"><div class="t">${esc(label)}</div><code>${esc(k)}</code></div>
      <input type="checkbox" class="tg" data-svc="${esc(k)}" ${settingsDraft.services[k] ? "checked" : ""} aria-label="${esc(label)}"></label>`).join("");
  markDirty();
}
$("pMain").oninput = () => { settingsDraft.main = +$("pMain").value; markDirty(); };
$("pAudio").oninput = () => { settingsDraft.audio = +$("pAudio").value; markDirty(); };
$("pExtraAdd").onclick = () => {
  const p = +$("pExtraNew").value;
  if (!p || p < 1 || p > 65535) return toast("Enter a port between 1 and 65535");
  if (p === settingsDraft.main || settingsDraft.extra.includes(p)) return toast(`Port ${p} is already listed`);
  settingsDraft.extra.push(p); settingsDraft.extra.sort((a, b) => a - b);
  $("pExtraNew").value = ""; renderSettings();
};
$("pExtraNew").onkeydown = (e) => { if (e.key === "Enter") $("pExtraAdd").click(); };
$("pExtra").onclick = (e) => {
  const b = e.target.closest("[data-rmport]"); if (!b) return;
  settingsDraft.extra = settingsDraft.extra.filter(p => p !== +b.dataset.rmport); renderSettings();
};
$("svcList").onchange = (e) => {
  if (!e.target.dataset.svc) return;
  settingsDraft.services[e.target.dataset.svc] = e.target.checked; markDirty();
};
$("saveSettings").onclick = async () => {
  if (!settingsChanged()) return toast("Nothing to save");
  const s = settingsDraft.services, warn = [];
  if (!s.gui) warn.push("• The web panel will turn off. You'll need the server to turn it back on:\n  sudo phonealert.py services enable gui");
  if (!s.web_settings && state.services.web_settings) warn.push("• Settings will lock. Unlock on the server with:\n  sudo phonealert.py services enable web_settings");
  if (!s.gui_login && state.services.gui_login) warn.push("• Anyone who can reach this page will be able to send alerts without a password.");
  if (settingsDraft.main !== state.ports.main) warn.push(`• The panel moves to port ${settingsDraft.main}. Phones check pushes on the port set in CME, so alerts can fail until CME is updated.`);
  if (warn.length && !confirm("Before saving:\n\n" + warn.join("\n\n") + "\n\nSave anyway?")) return;
  const oldMain = state.ports.main;
  $("saveSettings").disabled = true;
  try {
    const r = await api("/api/settings", { method: "POST", headers: { "Content-Type": "application/json" },
      body: JSON.stringify({ ports: { main: settingsDraft.main, audio: settingsDraft.audio, extra: settingsDraft.extra },
                             services: settingsDraft.services }) });
    const note = r.note ? `<p style="margin:8px 0 0"><b>Important:</b> ${esc(r.note)}</p>` : "";
    if (!r.services.gui) {
      banner(`The web panel is now off. Turn it back on from the server: <code>sudo phonealert.py services enable gui</code>`, "warn");
      document.querySelector("main").classList.add("hidden"); return;
    }
    if (r.restarting) {
      const urls = [r.ports.main, ...r.ports.extra].map(p => `<code>http://${esc(state.server_host)}:${p}/</code>`).join(", ");
      const moved = r.ports.main !== oldMain && !r.ports.extra.includes(oldMain);
      banner(`Saved. The server is restarting with web ports ${urls}.` + (moved
        ? ` This page's port is no longer used, so open one of those addresses (and update any ISR port forward that points at ${oldMain}).`
        : " This page reloads in a few seconds.") + note, note ? "warn" : "info");
      if (!moved) setTimeout(() => location.reload(), 3500);
    } else {
      banner(note ? `Saved.${note}` : "", "warn");
      toast("Settings saved");
      await refresh(); loadSettingsDraft(); renderSettings(); renderPhoneEdit();
    }
  } catch (err) { toast(err.message); }
  finally { $("saveSettings").disabled = false; }
};
$("phoneEdit").addEventListener("input", (e) => {
  const i = e.target.dataset.i; if (i === undefined) return;
  phoneDraft[+i][e.target.dataset.k] = e.target.value;
});
$("phoneEdit").addEventListener("click", (e) => {
  const b = e.target.closest("[data-rm]"); if (!b) return;
  phoneDraft.splice(+b.dataset.rm, 1); renderPhoneEdit();
});
$("addPhone").onclick = () => { phoneDraft.push({ name: "", ip: "" }); renderPhoneEdit();
  const ins = $("phoneEdit").querySelectorAll('input[data-k="name"]'); ins[ins.length - 1]?.focus(); };
$("savePhones").onclick = async () => {
  const clean = phoneDraft.filter(p => p.ip.trim()).map(p => ({ name: p.name.trim() || p.ip.trim(), ip: p.ip.trim() }));
  try {
    const r = await api("/api/phones", { method: "POST", headers: { "Content-Type": "application/json" }, body: JSON.stringify(clean) });
    const added = r.phones.filter(p => !state.phones.some(o => o.ip === p.ip)).map(p => p.ip);
    await refresh(); added.forEach(ip => selected.add(ip)); renderTargets();
    toast("Phones saved");
  } catch (err) { toast(err.message); }
};

function renderHistory() {
  if (!on("history")) { $("history").innerHTML = `<div class="empty">Alert history is turned off in Settings.</div>`; return; }
  $("history").innerHTML = state.history.length ?state.history.map(h => `
    <div class="item"><div class="grow">
      <div class="t">${esc(h.title)}${h.sound ? ` <span class="hint">♪ ${esc(h.sound)}${h.repeat > 1 ? ` ×${h.repeat}` : ""}</span>` : ""}</div>
      ${h.text ? `<div class="s">${esc(h.text)}</div>` : ""}
      <div class="s">${ago(h.ts)} · ${h.ok}/${h.total} phones · ${esc((h.targets || []).join(", "))}</div>
    </div></div>`).join("") : `<div class="empty">Nothing sent yet.</div>`;
}

function renderStreaming() {
  const s = state.streaming;
  $("streaming").innerHTML = s ? `<span class="pill"><span class="pulse"></span>Playing ${esc(s.sound)}
      <button class="primary" id="stopAudio" type="button">Stop</button></span>` : "";
  if (s) $("stopAudio").onclick = async () => {
    try { await api("/api/stop", { method: "POST" }); toast("Audio stopped"); refresh(); } catch (err) { toast(err.message); }
  };
}

async function refresh() {
  state = await api("/api/state");
  applyServices();
  renderTargets(); renderSounds(); renderHistory(); renderStreaming();
  if (!settingsDraft) { loadSettingsDraft(); renderSettings(); }
  $("ffmpegNote").innerHTML = state.ffmpeg ? "" : `<div class="note">ffmpeg isn't installed, so sounds can't be uploaded. Run: sudo apt install ffmpeg</div>`;
  $("upMax").textContent = state.limits.upload_mb; $("secMax").textContent = state.limits.seconds;
  if (!$("repeat").options.length) {
    $("repeat").innerHTML = Array.from({ length: state.limits.repeat }, (_, i) =>
      `<option value="${i + 1}">${i + 1 === 1 ? "Once" : `${i + 1} times`}</option>`).join("");
  }
}

$("send").onclick = async () => {
  const body = {
    title: $("title").value.trim() || "ALERT",
    text: $("text").value.trim(),
    sound: on("audio") ? $("sound").value : "",
    repeat: +$("repeat").value || 1,
    volume: $("volume").value ? +$("volume").value : null,
    phones: [...selected],
  };
  if (!body.phones.length) return toast("Select at least one phone");
  if (!body.text && !body.sound) return toast("Type a message or choose a sound");
  const names = state.phones.filter(p => selected.has(p.ip)).map(p => p.name).join(", ");
  if (!confirm(`Send "${body.title}" to ${body.phones.length} phone(s)?\n\n${names}`)) return;
  $("send").disabled = true; $("send").textContent = "Sending…"; $("results").innerHTML = "";
  try {
    const r = await api("/api/send", { method: "POST", headers: { "Content-Type": "application/json" }, body: JSON.stringify(body) });
    $("results").innerHTML = r.results.map(x => `
      <div class="res ${x.ok ? "ok" : "bad"}"><span class="tag">${x.ok ? "OK" : "FAIL"}</span>
        <span>${esc(x.name)}</span><span class="msg">${x.ok ? esc(x.ip) : esc(x.message)}</span></div>`).join("");
    const ok = r.results.filter(x => x.ok).length;
    toast(`${ok} of ${r.results.length} phones accepted the alert`);
    refresh();
  } catch (err) { toast(err.message); }
  finally { $("send").disabled = false; $("send").textContent = "Send alert"; }
};

$("title").oninput = updateCount;
renderPresets();
refresh().then(() => { phoneDraft = state.phones.map(p => ({ ...p })); renderPhoneEdit(); })
  .catch(err => toast("Could not load: " + err.message));
setInterval(() => { api("/api/state").then(s => { const was = JSON.stringify(state.streaming); state.streaming = s.streaming; state.history = s.history;
  if (was !== JSON.stringify(s.streaming)) renderStreaming(); renderHistory(); }).catch(() => {}); }, 3000);
</script>
</body>
</html>
PAHTMLEOF
chmod 755 "$BIN"
chmod 644 "$UI_DIR/index.html"
ok "installed $BIN and $UI_DIR/index.html"

say "Writing ${CONFIG}"
NEWPASS=$(head -c 48 /dev/urandom | base64 | tr -dc 'A-Za-z0-9' | head -c 24)
NEWADMIN=$(head -c 48 /dev/urandom | base64 | tr -dc 'A-Za-z0-9' | head -c 12)
SERVER_IP="$SERVER_IP" PORT="$PORT" PUSH_USER="$PUSH_USER" NEWPASS="$NEWPASS" NEWADMIN="$NEWADMIN" \
DEFAULT_PHONES="$DEFAULT_PHONES" python3 - "$CONFIG" <<'EOF'
import json, os, sys
path = sys.argv[1]
try:
    cfg = json.load(open(path))
    print("    keeping existing passwords and phone list")
except (OSError, ValueError):
    cfg = {}
env = os.environ
# keep a main port chosen in the GUI / "ports main" on re-runs
cfg["listen_port"] = int(cfg.get("listen_port") or env["PORT"])
cfg["server_url"] = f"http://{env['SERVER_IP']}:{cfg['listen_port']}"
cfg.setdefault("extra_ports", [])
cfg.setdefault("services", {})
cfg.setdefault("push_user", env["PUSH_USER"])
cfg.setdefault("push_password", env["NEWPASS"])
cfg.setdefault("admin_user", "admin")
if not cfg.get("admin_password"):
    cfg["admin_password"] = env["NEWADMIN"]
cfg.setdefault("data_dir", "/var/lib/phonealert")
cfg.setdefault("rtp_port", 20480)
cfg.setdefault("rtprx_uri", "RTPRx:{phone_ip}:{port}")
cfg.setdefault("rtprx_stop_uri", "RTPRx:Stop")
if not cfg.get("phones"):
    cfg["phones"] = []
    for item in env["DEFAULT_PHONES"].split(","):
        name, ip = item.split("=")
        cfg["phones"].append({"ip": ip, "name": name})
# upgrade old plain-IP lists to named entries, using known extension names
known = dict(reversed(i.split("=")) for i in env["DEFAULT_PHONES"].split(","))
up = []
for p in cfg["phones"]:
    p = p if isinstance(p, dict) else {"ip": p, "name": p}
    if p.get("name", p["ip"]) == p["ip"] and p["ip"] in known:
        p["name"] = known[p["ip"]]
    up.append(p)
cfg["phones"] = up
tmp = path + ".tmp"
with open(tmp, "w") as f:
    json.dump(cfg, f, indent=2)
os.chmod(tmp, 0o600)
os.replace(tmp, path)
EOF
mkdir -p /var/lib/phonealert
ok "config ready"

say "Installing systemd service"
cat > "$UNIT" <<EOF
[Unit]
Description=Cisco phone alert server (web GUI + push)
After=network-online.target
Wants=network-online.target

[Service]
ExecStart=${BIN} serve
StateDirectory=phonealert
Restart=always

[Install]
WantedBy=multi-user.target
EOF
systemctl daemon-reload
systemctl enable phonealert >/dev/null 2>&1
systemctl restart phonealert
sleep 1.5
if systemctl is-active --quiet phonealert; then
  ok "phonealert service is running"
else
  warn "service failed to start - recent log:"
  journalctl -u phonealert -n 20 --no-pager
  exit 1
fi

read_cfg() { python3 -c "import json;print(json.load(open('$CONFIG'))['$1'])"; }
PORT=$(read_cfg listen_port)
ALLPORTS=$(python3 -c "import json;c=json.load(open('$CONFIG'));print(' '.join(str(p) for p in [c['listen_port']]+c.get('extra_ports',[])))")

if command -v ufw >/dev/null && ufw status | grep -q "Status: active"; then
  say "Opening web port(s) ${ALLPORTS} in ufw"
  for p in $ALLPORTS; do ufw allow "${p}/tcp" >/dev/null; done
  ok "ufw rules added"
fi

PASS=$(read_cfg push_password); AUSER=$(read_cfg admin_user); APASS=$(read_cfg admin_password)

say "Testing"
R=$(curl -s "http://127.0.0.1:${PORT}/auth?UserID=${PUSH_USER}&Password=${PASS}" || true)
if [[ "$R" == "AUTHORIZED" ]]; then ok "phone auth endpoint answers AUTHORIZED"; else warn "auth answered: '${R}'"; fi
C=$(curl -s -o /dev/null -w '%{http_code}' -u "${AUSER}:${APASS}" "http://127.0.0.1:${PORT}/" || true)
if [[ "$C" == "200" ]]; then ok "web GUI is up"; else warn "web GUI returned HTTP ${C}"; fi
for ip in $(python3 -c "import json;print(' '.join(p['ip'] for p in json.load(open('$CONFIG'))['phones']))"); do
  code=$(curl -s -o /dev/null -m 3 -w '%{http_code}' "http://${ip}/" || true)
  if [[ "$code" =~ ^[23] ]]; then ok "${ip} web server on"
  else warn "${ip} not reachable (code ${code}) - web access off or phone offline"; fi
done

cat <<EOF

=====================================================================
  Web GUI:   http://${SERVER_IP}:${PORT}/
  Login:     ${AUSER}  /  ${APASS}
  (stored in ${CONFIG}; view it any time with: sudo cat ${CONFIG})
=====================================================================

Command line:
  sudo phonealert.py send "Drop, cover and hold on" -t "EARTHQUAKE WARNING"
  sudo phonealert.py send "Fire drill" --sound Siren --repeat 3 --phone 192.168.10.2
  sudo phonealert.py sounds
  sudo phonealert.py ports                     (ports main|audio|add|remove N)
  sudo phonealert.py services                  (services enable|disable NAME)
  sudo phonealert.py phones                    (phones add IP NAME | remove IP)

Status / logs:  systemctl status phonealert   |   journalctl -u phonealert -f
EOF
