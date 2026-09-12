/* ===========================================================================
   BloxSwap — backend
   No dependencies. Needs Node 18+.        Run:  node server.js
   All data lives in data.json next to this file.
   =========================================================================== */
import http from "node:http";
import fs from "node:fs";
import fsp from "node:fs/promises";
import path from "node:path";
import crypto from "node:crypto";
import { fileURLToPath } from "node:url";

const __dirname = path.dirname(fileURLToPath(import.meta.url));
const PORT = process.env.PORT || 3000;
const DATA_FILE = path.join(__dirname, "data.json");
const PUBLIC_DIR = path.join(__dirname, "public");

/* Staff credentials, stored as SHA-256. Never sent to the browser.
   Override with env vars ADMIN_USER_HASH / ADMIN_PASS_HASH in production. */
const ADMIN = {
  user: process.env.ADMIN_USER_HASH || "46a5a446373f5bcf823f02232bb2b52b020f4d8ac09a290462662f682f8801e3",
  pass: process.env.ADMIN_PASS_HASH || "2671d930a302ea7e52a042c25c10df17852919485b7e0187b7f50d0afad948d1"
};
const sha256 = s => crypto.createHash("sha256").update(String(s)).digest("hex");

const DEFAULT_SETTINGS = {
  commissionPct: 8, minWithdrawal: 10, warrantyHours: 48,
  siteNotice: "", maintenance: false, signupsOpen: true, listingsOpen: true,
  brandColor: "#EA5B0C", secondaryColor: "#3F4652", featuredColor: "#191A18", verifiedColor: "#1C8C55",
  announce: null, minDeposit: 5,
  wallets: { "Bitcoin (BTC)": "", "Ethereum (ETH)": "", "Litecoin (LTC)": "", "USDT (TRC-20)": "" }
};
const HEX_RE = /^#[0-9a-fA-F]{6}$/;
function safeHex(v, fallback) { return HEX_RE.test(v || "") ? v : fallback; }

/* ===========================================================================
   Persistence
   =========================================================================== */
const blank = () => ({
  users: [], listings: [], orders: [], withdrawals: [], claims: [],
  tickets: [], raffles: [], deposits: [], audit: [], sessions: {}, staffSeen: 0, settings: { ...DEFAULT_SETTINGS }
});
let db = blank();
try {
  if (fs.existsSync(DATA_FILE)) {
    db = { ...blank(), ...JSON.parse(fs.readFileSync(DATA_FILE, "utf8")) };
    db.settings = { ...DEFAULT_SETTINGS, ...(db.settings || {}) };
    /* one-time cleanup: drop any demo accounts left over from earlier builds */
    const demoMails = ["vault@example.com", "night@example.com", "quick@example.com"];
    const demos = db.users.filter(u => demoMails.includes((u.email || "").toLowerCase()));
    if (demos.length) {
      const ids = new Set(demos.map(u => u.uid));
      db.users = db.users.filter(u => !ids.has(u.uid));
      db.listings = db.listings.filter(l => !ids.has(l.sellerUid));
      console.log(`  Removed ${demos.length} leftover demo account(s).`);
    }
  }
} catch (e) { console.error("data.json unreadable, starting fresh:", e.message); }

let saveTimer = null, writing = false, dirty = false;
function save() {
  dirty = true;
  clearTimeout(saveTimer);
  saveTimer = setTimeout(flush, 80);
}
async function flush() {
  if (writing) { save(); return; }
  writing = true; dirty = false;
  try {
    const tmp = DATA_FILE + ".tmp";
    await fsp.writeFile(tmp, JSON.stringify(db));
    await fsp.rename(tmp, DATA_FILE);
  } catch (e) { console.error("save failed:", e.message); }
  writing = false;
  if (dirty) save();
}
function flushSync() { try { fs.writeFileSync(DATA_FILE, JSON.stringify(db)); } catch {} }
process.on("SIGINT", () => { flushSync(); process.exit(0); });
process.on("SIGTERM", () => { flushSync(); process.exit(0); });
setInterval(flushSync, 60000).unref();

const S = k => db.settings[k] ?? DEFAULT_SETTINGS[k];
const now = () => Date.now();
const rid = p => p + Date.now().toString(36) + crypto.randomBytes(3).toString("hex");
const round2 = n => Math.round((n + Number.EPSILON) * 100) / 100;
const money = n => "$" + round2(n).toFixed(2);
const userBy = uid => db.users.find(u => u.uid === uid) || null;

function newUid() {
  let n; do { n = String(crypto.randomInt(100000, 1000000)); } while (db.users.some(u => u.uid === n));
  return n;
}
function newTicketNo() {
  let n; do { n = "BS-" + crypto.randomInt(100000, 1000000); } while (db.tickets.some(t => t.no === n));
  return n;
}
function audit(action, detail, actor = "system") {
  db.audit.unshift({ id: rid("a_"), t: now(), action, detail, actor });
  db.audit = db.audit.slice(0, 2000);
}

/* ===========================================================================
   Passwords + sessions
   =========================================================================== */
const hashPassword = pw => {
  const salt = crypto.randomBytes(16).toString("hex");
  return `scrypt$${salt}$${crypto.scryptSync(pw, salt, 64).toString("hex")}`;
};
function checkPassword(pw, stored) {
  if (!stored?.startsWith("scrypt$")) return false;
  const [, salt, key] = stored.split("$");
  try {
    return crypto.timingSafeEqual(Buffer.from(key, "hex"),
      Buffer.from(crypto.scryptSync(pw, salt, 64).toString("hex"), "hex"));
  } catch { return false; }
}
const SESSION_MS = 1000 * 60 * 60 * 24 * 30;
const cookieFor = t => `bs_session=${t}; HttpOnly; Path=/; Max-Age=${SESSION_MS / 1000}; SameSite=Lax`;
const CLEAR_COOKIE = "bs_session=; HttpOnly; Path=/; Max-Age=0; SameSite=Lax";

function makeSession(uid, admin = false) {
  const token = crypto.randomBytes(32).toString("hex");
  db.sessions[token] = { uid, admin, created: now(), expires: now() + SESSION_MS };
  save();
  return token;
}
function getSession(req) {
  const m = (req.headers.cookie || "").match(/(?:^|;\s*)bs_session=([a-f0-9]{64})/);
  if (!m) return null;
  const s = db.sessions[m[1]];
  if (!s) return null;
  if (s.expires < now()) { delete db.sessions[m[1]]; save(); return null; }
  return { token: m[1], ...s };
}
const sessionUser = req => { const s = getSession(req); return s ? userBy(s.uid) : null; };
const isAdmin = req => !!getSession(req)?.admin;

/* Staff-only IP history. Legitimate for fraud/abuse handling on your own
   service. Never exposed through publicUser — only adminUser. */
function recordIp(u, ip) {
  if (!ip || ip === "?") return;
  u.lastIp = ip;
  u.ipHistory = u.ipHistory || [];
  const existing = u.ipHistory.find(e => e.ip === ip);
  if (existing) existing.at = now();
  else u.ipHistory.unshift({ ip, at: now() });
  // keep the 10 most recently seen
  u.ipHistory = u.ipHistory.sort((a, b) => b.at - a.at).slice(0, 10);
}
function publicUser(u) {
  if (!u) return null;
  return {
    uid: u.uid, username: u.username, email: u.email,
    buyerBalance: round2(u.buyerBalance), sellerBalance: round2(u.sellerBalance),
    verified: !!u.verified, banned: !!u.banned,
    roblox: u.roblox || null,
    pendingRoblox: u.pendingRoblox ? { id: u.pendingRoblox.id, name: u.pendingRoblox.name, phrase: u.pendingRoblox.phrase } : null,
    receivingAccounts: (u.receivingAccounts || []).map(a => ({ id: a.id, name: a.name })),
    createdAt: u.createdAt, lastLogin: u.lastLogin
  };
}
const adminUser = u => ({ ...publicUser(u), loginCount: u.loginCount || 0, notes: u.notes || "",
  lastIp: u.lastIp || null, ipHistory: u.ipHistory || [] });

/* ===========================================================================
   Roblox API — everything cached so the UI feels instant
   =========================================================================== */
const UA = { "User-Agent": "Mozilla/5.0 (compatible; BloxSwap/1.0)", Accept: "application/json" };
const cache = new Map();
const cacheGet = (k, ttl) => { const h = cache.get(k); return h && now() - h.t < ttl ? h.v : undefined; };
const cacheSet = (k, v) => { cache.set(k, { t: now(), v }); return v; };

async function rbxGet(url, ms = 8000) {
  const res = await fetch(url, { headers: UA, signal: AbortSignal.timeout(ms) });
  if (!res.ok) throw new Error(`Roblox returned ${res.status}`);
  return res.json();
}
async function rbxPost(url, body, ms = 8000) {
  const res = await fetch(url, {
    method: "POST", headers: { ...UA, "Content-Type": "application/json" },
    body: JSON.stringify(body), signal: AbortSignal.timeout(ms)
  });
  if (!res.ok) throw new Error(`Roblox returned ${res.status}`);
  return res.json();
}

/* exact username → account (one request) */
async function robloxByUsername(username) {
  const key = "un:" + username.toLowerCase();
  const hit = cacheGet(key, 5 * 60000); if (hit) return hit;
  const d = await rbxPost("https://users.roblox.com/v1/usernames/users",
    { usernames: [username], excludeBannedUsers: false });
  const u = (d.data || [])[0];
  if (!u) throw new Error("No Roblox account with that username.");
  return cacheSet(key, { id: u.id, name: u.name, display: u.displayName || u.name });
}
const robloxProfile = id => rbxGet(`https://users.roblox.com/v1/users/${id}`);

async function robloxCollectibles(id, { force = false } = {}) {
  const key = "inv:" + id;
  if (!force) { const hit = cacheGet(key, 45000); if (hit) return hit; }
  let out = [], cursor = "", guard = 0;
  do {
    const d = await rbxGet(`https://inventory.roblox.com/v1/users/${id}/assets/collectibles`
      + `?sortOrder=Asc&limit=100${cursor ? `&cursor=${encodeURIComponent(cursor)}` : ""}`);
    for (const c of d.data || []) out.push({
      uaid: String(c.userAssetId), assetId: c.assetId, name: c.name,
      serial: c.serialNumber ?? null, rap: c.recentAveragePrice ?? 0
    });
    cursor = d.nextPageCursor || "";
  } while (cursor && ++guard < 12);
  return cacheSet(key, out);
}
async function robloxCanView(id) {
  try { return (await rbxGet(`https://inventory.roblox.com/v1/users/${id}/can-view-inventory`)).canView !== false; }
  catch { return true; }
}

/* thumbnails.roblox.com — batched and cached for an hour */
async function thumbUrl(kind, id) {
  const key = `t${kind}:${id}`;
  const hit = cacheGet(key, 3600000); if (hit !== undefined) return hit;
  try {
    const url = kind === "a"
      ? `https://thumbnails.roblox.com/v1/assets?assetIds=${id}&size=420x420&format=Png&isCircular=false`
      : `https://thumbnails.roblox.com/v1/users/avatar-headshot?userIds=${id}&size=150x150&format=Png&isCircular=false`;
    const d = await rbxGet(url, 6000);
    return cacheSet(key, (d.data || [])[0]?.imageUrl || "");
  } catch { return cacheSet(key, ""); }
}

/* Rolimons value/demand — refreshed in the background, never blocks a request */
let valueIndex = new Map();
async function refreshValues() {
  try {
    const res = await fetch("https://www.rolimons.com/itemapi/itemdetails", {
      headers: { ...UA, Referer: "https://www.rolimons.com/" }, signal: AbortSignal.timeout(12000)
    });
    if (!res.ok) return;
    const d = await res.json();
    const m = new Map();
    for (const [id, a] of Object.entries(d.items || {}))
      m.set(+id, { name: a[0], acr: a[1] || "", rap: a[2], value: a[3], demand: a[5], trend: a[6], projected: a[7] === 1 });
    valueIndex = m;
  } catch {}
}
refreshValues();
setInterval(refreshValues, 10 * 60000).unref();
const valueOf = assetId => valueIndex.get(assetId) || null;

/* ===========================================================================
   Verification phrase
   =========================================================================== */
const WORDS = ("cinder north pepper reactor topaz amber quartz harbor lantern maple velvet cobalt ember thistle "
  + "marble orbit copper juniper falcon dune saffron pixel granite willow nova basil onyx tundra plaza cedar "
  + "mango prism gable clover ridge lumen sable citrus vault aspen quiver mosaic bramble kelp signal drift "
  + "lilac forge peak nectar canyon ripple beacon meadow anchor").split(" ");
const makePhrase = (n = 5) => {
  const pool = [...WORDS], out = [];
  for (let i = 0; i < n; i++) out.push(pool.splice(crypto.randomInt(pool.length), 1)[0]);
  return out.join(" ");
};
const norm = s => String(s || "").toLowerCase().replace(/[^a-z0-9 ]/g, " ").replace(/\s+/g, " ").trim();

/* ===========================================================================
   HTTP helpers
   =========================================================================== */
function send(res, code, obj, headers = {}) {
  res.writeHead(code, { "Content-Type": "application/json; charset=utf-8", "Cache-Control": "no-store", ...headers });
  res.end(JSON.stringify(obj));
}
const ok = (res, o = {}) => send(res, 200, o);
const fail = (res, code, msg) => send(res, code, { error: msg });

const readBody = req => new Promise((resolve, reject) => {
  let raw = "";
  req.on("data", c => { raw += c; if (raw.length > 2e6) { reject(new Error("Body too large")); req.destroy(); } });
  req.on("end", () => { try { resolve(raw ? JSON.parse(raw) : {}); } catch { reject(new Error("Bad JSON")); } });
  req.on("error", reject);
});

const MIME = { ".html": "text/html", ".js": "text/javascript", ".css": "text/css",
  ".svg": "image/svg+xml", ".png": "image/png", ".ico": "image/x-icon", ".json": "application/json" };
async function serveStatic(res, url) {
  const file = path.join(PUBLIC_DIR, path.normalize(url === "/" ? "/index.html" : url).replace(/^(\.\.[/\\])+/, ""));
  if (!file.startsWith(PUBLIC_DIR)) return fail(res, 403, "Forbidden");
  try {
    const data = await fsp.readFile(file);
    res.writeHead(200, { "Content-Type": MIME[path.extname(file)] || "application/octet-stream" });
    res.end(data);
  } catch {
    try {
      const data = await fsp.readFile(path.join(PUBLIC_DIR, "index.html"));
      res.writeHead(200, { "Content-Type": "text/html" }); res.end(data);
    } catch { fail(res, 404, "Not found"); }
  }
}

const hits = new Map();
function throttle(ip, key, max, windowMs) {
  const k = ip + ":" + key, rec = hits.get(k) || { n: 0, t: now() };
  if (now() - rec.t > windowMs) { rec.n = 0; rec.t = now(); }
  rec.n++; hits.set(k, rec);
  return rec.n <= max;
}

/* ===========================================================================
   Views
   =========================================================================== */
const PAYMENT_METHODS = ["Crypto", "PayPal", "Cash App", "Credit card"];
function listingView(l) {
  const seller = userBy(l.sellerUid);
  const v = valueOf(l.assetId);
  return {
    id: l.id, assetId: l.assetId, name: l.name, serial: l.serial, price: round2(l.price),
    status: l.status, featured: !!l.featured, createdAt: l.createdAt,
    warrantyHours: l.warrantyHours ?? S("warrantyHours"),
    rap: l.rap ?? v?.rap ?? null, value: v?.value ?? null, demand: v?.demand ?? -1,
    projected: !!v?.projected, house: !!l.house,
    paymentMethods: (Array.isArray(l.paymentMethods) && l.paymentMethods.length) ? l.paymentMethods : PAYMENT_METHODS,
    /* Seller identity is deliberately withheld until a buyer owns the order —
       it only ever reaches the buyer through orderView. */
    seller: { verified: !!seller?.verified }
  };
}
/* Orders show both sides' Roblox usernames so the seller knows exactly who to trade. */
function orderView(o, forUid) {
  const other = userBy(o.buyerUid === forUid ? o.sellerUid : o.buyerUid);
  const isBuyer = o.buyerUid === forUid;
  return {
    id: o.id, name: o.name, assetId: o.assetId, serial: o.serial ?? null,
    price: round2(o.price), payout: round2(o.payout), fee: round2(o.fee),
    status: o.status, createdAt: o.createdAt, warrantyEnds: o.warrantyEnds || null,
    warrantyHours: o.warrantyHours, role: isBuyer ? "buyer" : "seller",
    counterparty: isBuyer ? o.sellerUid : o.buyerUid,
    counterpartyName: other?.username || "(deleted)",
    /* Buyer sees who's sending the trade (the seller's verified account).
       Seller sees where to send it (the receiving account the buyer chose at checkout) —
       that may not be the buyer's own verified selling account, and that's fine. */
    counterpartyRoblox: isBuyer
      ? (other?.roblox ? { id: other.roblox.id, name: other.roblox.name } : null)
      : (o.receiving ? { id: o.receiving.id, name: o.receiving.name } : null),
    paymentMethod: o.paymentMethod || null,
    house: !!o.house,
    hasClaim: db.claims.some(c => c.orderId === o.id)
  };
}
const ticketView = t => ({
  id: t.id, no: t.no, subject: t.subject, category: t.category, status: t.status,
  createdAt: t.createdAt, updatedAt: t.updatedAt, unread: !!t.unreadUser,
  messages: t.messages.map(m => ({ from: m.from, text: m.text, t: m.t }))
});

/* ===========================================================================
   Routes
   =========================================================================== */
const routes = [];
const route = (method, pattern, handler) => routes.push({ method, pattern, handler });
const needUser = (req, res) => { const u = sessionUser(req); if (!u) { fail(res, 401, "Log in first."); return null; } return u; };
const needAdmin = (req, res) => { if (!isAdmin(req)) { fail(res, 403, "Staff access required."); return false; } return true; };

/* ---- bootstrap ---- */
route("GET", /^\/api\/bootstrap$/, async (req, res) => {
  const u = sessionUser(req);
  send(res, 200, {
    user: publicUser(u), admin: isAdmin(req),
    settings: {
      commissionPct: S("commissionPct"), minWithdrawal: S("minWithdrawal"),
      warrantyHours: S("warrantyHours"), siteNotice: S("siteNotice"),
      brandColor: S("brandColor"), secondaryColor: S("secondaryColor"),
      featuredColor: S("featuredColor"), verifiedColor: S("verifiedColor"),
      announce: db.settings.announce || null,
      maintenance: S("maintenance"), signupsOpen: S("signupsOpen"), listingsOpen: S("listingsOpen")
    },
    unread: u ? db.tickets.filter(t => t.uid === u.uid && t.unreadUser).length : 0,
    staff: isAdmin(req) ? staffAlerts() : null
  });
});

/* Everything a staff member should know about at a glance. */
function staffAlerts() {
  const seen = db.staffSeen || 0;
  const tickets = db.tickets.filter(t => t.unreadStaff);
  const payouts = db.withdrawals.filter(w => w.status === "pending");
  const claims = db.claims.filter(c => c.status === "open");
  const signups = db.users.filter(u => u.createdAt > seen);
  const claimed = new Set(db.claims.map(c => c.orderId));
  const escrow = db.orders.filter(o => o.status === "escrow" && now() - o.createdAt > 864e5 && !claimed.has(o.id));
  const items = [];
  for (const t of tickets.slice(0, 8)) items.push({
    kind: "ticket", id: t.no, t: t.updatedAt, title: t.subject,
    detail: `${userBy(t.uid)?.username || "user"} · ${t.no}`, href: `#/admin/tickets/${t.no}`
  });
  for (const w of payouts.slice(0, 8)) items.push({
    kind: "payout", t: w.createdAt, title: `${money(w.amount)} withdrawal via ${w.method}`,
    detail: `Seller#${w.uid} · ${userBy(w.uid)?.username || "user"}`, href: "#/admin/payouts"
  });
  for (const c of claims.slice(0, 8)) items.push({
    kind: "claim", t: c.createdAt, title: "Warranty claim",
    detail: `Seller#${c.uid} · ${db.orders.find(o => o.id === c.orderId)?.name || ""}`, href: "#/admin/claims"
  });
  for (const u of signups.slice(0, 8)) items.push({
    kind: "signup", t: u.createdAt, title: `${u.username} signed up`,
    detail: `Seller#${u.uid}`, href: "#/admin/users"
  });
  for (const o of escrow.slice(0, 5)) items.push({
    kind: "stuck", t: o.createdAt, title: `${o.name} stuck in escrow`,
    detail: `over 24h · Seller#${o.sellerUid} hasn't delivered`, href: "#/admin/orders"
  });
  const undrawn = db.raffles.filter(r => r.status === "ended" && !r.winnerUid);
  for (const r of undrawn.slice(0, 4)) items.push({
    kind: "raffle", t: r.endsAt, title: `${r.name} raffle ended`,
    detail: `${r.entries.length} entries — draw a winner`, href: "#/admin/raffles"
  });
  items.sort((a, b) => b.t - a.t);
  return {
    tickets: tickets.length, payouts: payouts.length, claims: claims.length,
    signups: signups.length, stuck: escrow.length, raffles: undrawn.length,
    total: tickets.length + payouts.length + claims.length + signups.length + escrow.length + undrawn.length,
    items: items.slice(0, 14)
  };
}
route("POST", /^\/api\/admin\/seen$/, async (req, res, _m, body) => {
  if (!needAdmin(req, res)) return;
  const kind = body.kind || "all";
  if (kind === "all" || kind === "signup") db.staffSeen = now();
  if (kind === "all" || kind === "ticket") db.tickets.forEach(t => t.unreadStaff = 0);
  save(); send(res, 200, { staff: staffAlerts() });
});

/* ---- auth ---- */
/* Unauthenticated on purpose — colours and the notice banner aren't sensitive,
   and every visitor (logged in or not) needs to pick up live changes. */
route("GET", /^\/api\/theme$/, async (req, res) => {
  send(res, 200, {
    brandColor: S("brandColor"), secondaryColor: S("secondaryColor"),
    featuredColor: S("featuredColor"), verifiedColor: S("verifiedColor"),
    announce: db.settings.announce || null,
    siteNotice: S("siteNotice"), maintenance: S("maintenance")
  }, { "Cache-Control": "no-store" });
});

route("POST", /^\/api\/signup$/, async (req, res, _m, body, ip) => {
  if (!S("signupsOpen")) return fail(res, 403, "Signups are closed right now.");
  if (!throttle(ip, "signup", 6, 3600000)) return fail(res, 429, "Too many signups from this network.");
  const username = String(body.username || "").trim();
  const email = String(body.email || "").trim().toLowerCase();
  const password = String(body.password || "");
  if (username.length < 3 || username.length > 20) return fail(res, 400, "Username must be 3–20 characters.");
  if (!/^[a-zA-Z0-9_]+$/.test(username)) return fail(res, 400, "Username can use letters, numbers and underscores only.");
  if (!/^[^@\s]+@[^@\s]+\.[^@\s]+$/.test(email)) return fail(res, 400, "That email doesn't look right.");
  if (password.length < 8) return fail(res, 400, "Password needs at least 8 characters.");
  if (db.users.some(u => u.username.toLowerCase() === username.toLowerCase())) return fail(res, 409, "That username is taken.");
  if (db.users.some(u => u.email === email)) return fail(res, 409, "An account already uses that email.");
  const u = {
    uid: newUid(), username, email, pass: hashPassword(password),
    buyerBalance: 0, sellerBalance: 0, verified: false, banned: false,
    roblox: null, pendingRoblox: null, createdAt: now(), lastLogin: now(), loginCount: 1, notes: ""
  };
  db.users.push(u);
  recordIp(u, ip);
  audit("user.signup", `Seller#${u.uid} (${username}) signed up`, username);
  const token = makeSession(u.uid);
  save();
  send(res, 200, { user: publicUser(u) }, { "Set-Cookie": cookieFor(token) });
});

route("POST", /^\/api\/login$/, async (req, res, _m, body, ip) => {
  if (!throttle(ip, "login", 12, 900000)) return fail(res, 429, "Too many attempts. Wait a few minutes.");
  const id = String(body.id || "").trim().toLowerCase();
  const u = db.users.find(x => x.username.toLowerCase() === id || x.email === id || x.uid === id);
  if (!u || u.house || !checkPassword(String(body.password || ""), u.pass)) return fail(res, 401, "Wrong username or password.");
  if (u.banned) return fail(res, 403, "This account is suspended. Contact support.");
  u.lastLogin = now(); u.loginCount = (u.loginCount || 0) + 1; recordIp(u, ip);
  const token = makeSession(u.uid);
  save();
  send(res, 200, { user: publicUser(u) }, { "Set-Cookie": cookieFor(token) });
});

route("POST", /^\/api\/logout$/, async (req, res) => {
  const s = getSession(req);
  if (s) { delete db.sessions[s.token]; save(); }
  send(res, 200, { ok: true }, { "Set-Cookie": CLEAR_COOKIE });
});

route("POST", /^\/api\/password$/, async (req, res, _m, body) => {
  const u = needUser(req, res); if (!u) return;
  if (!checkPassword(String(body.current || ""), u.pass)) return fail(res, 403, "Your current password is wrong.");
  if (String(body.next || "").length < 8) return fail(res, 400, "New password needs 8 characters.");
  u.pass = hashPassword(body.next);
  audit("user.password", `Seller#${u.uid} changed their own password`, u.username);
  save(); ok(res);
});

/* ---- Roblox verification ---- */
route("POST", /^\/api\/roblox\/start$/, async (req, res, _m, body, ip) => {
  const u = needUser(req, res); if (!u) return;
  if (!throttle(ip, "rbx", 30, 3600000)) return fail(res, 429, "Slow down a moment.");
  const name = String(body.username || "").trim();
  if (!name) return fail(res, 400, "Enter your Roblox username.");
  let found;
  try { found = await robloxByUsername(name); }
  catch (e) { return fail(res, 404, e.message.startsWith("No Roblox") ? e.message : "Couldn't reach Roblox. Try again."); }
  if (db.users.some(x => x.uid !== u.uid && x.roblox?.id === found.id))
    return fail(res, 409, "That Roblox account is already linked to another BloxSwap account.");
  u.pendingRoblox = { id: found.id, name: found.name, display: found.display, phrase: makePhrase(5), startedAt: now() };
  save();
  send(res, 200, { roblox: found, phrase: u.pendingRoblox.phrase });
});

route("POST", /^\/api\/roblox\/verify$/, async (req, res) => {
  const u = needUser(req, res); if (!u) return;
  const p = u.pendingRoblox;
  if (!p) return fail(res, 400, "Start verification first.");
  let profile;
  try { profile = await robloxProfile(p.id); }
  catch { return fail(res, 502, "Couldn't reach Roblox just then. Try once more."); }
  if (!norm(profile.description).includes(norm(p.phrase)))
    return fail(res, 400, "The phrase isn't in your description yet. Save your Roblox profile, then press verify again.");
  u.roblox = { id: p.id, name: profile.name || p.name, display: profile.displayName || p.display, linkedAt: now() };
  u.pendingRoblox = null;
  audit("roblox.verify", `Seller#${u.uid} verified as ${u.roblox.name} (${u.roblox.id})`, u.username);
  save();
  /* warm the inventory cache so the sell page loads instantly */
  robloxCollectibles(u.roblox.id, { force: true }).catch(() => {});
  send(res, 200, { roblox: u.roblox });
});

route("POST", /^\/api\/roblox\/cancel$/, async (req, res) => {
  const u = needUser(req, res); if (!u) return;
  u.pendingRoblox = null; save(); ok(res);
});

route("POST", /^\/api\/roblox\/unlink$/, async (req, res) => {
  const u = needUser(req, res); if (!u) return;
  db.listings.filter(l => l.sellerUid === u.uid && l.status === "active").forEach(l => l.status = "removed");
  u.roblox = null; u.pendingRoblox = null;
  audit("roblox.unlink", `Seller#${u.uid} unlinked their Roblox account`, u.username);
  save(); ok(res);
});

route("GET", /^\/api\/roblox\/inventory$/, async (req, res, _m, _b, _ip, url) => {
  const u = needUser(req, res); if (!u) return;
  if (!u.roblox) return fail(res, 400, "Verify your Roblox account first.");
  const force = url.searchParams.get("force") === "1";
  let items;
  try { items = await robloxCollectibles(u.roblox.id, { force }); }
  catch {
    if (!await robloxCanView(u.roblox.id))
      return fail(res, 403, "Your Roblox inventory is private. Turn it public in Roblox → Settings → Privacy, then reload.");
    return fail(res, 502, "Couldn't read your inventory from Roblox. Try again in a moment.");
  }
  if (!items.length && !await robloxCanView(u.roblox.id))
    return fail(res, 403, "Your Roblox inventory is private. Turn it public in Roblox → Settings → Privacy, then reload.");
  const listed = new Set(db.listings.filter(l => l.status === "active" && l.sellerUid === u.uid).map(l => l.uaid));
  send(res, 200, {
    items: items.map(c => ({ ...c, listed: listed.has(c.uaid), value: valueOf(c.assetId)?.value ?? null }))
  });
});

/* thumbnail redirects — real thumbnails.roblox.com, cached server-side */
route("GET", /^\/api\/thumb\/(asset|user)\/(\d+)$/, async (req, res, m) => {
  const url = await thumbUrl(m[1] === "asset" ? "a" : "u", m[2]);
  res.writeHead(302, { Location: url || "/placeholder.svg", "Cache-Control": "public, max-age=3600" });
  res.end();
});

/* Recently sold. Shows a trade the moment money changes hands (escrow onward),
   using the purchase time — so the rail moves as soon as someone buys, not only
   once delivery is confirmed. Refunded orders drop back off. No usernames. */
route("GET", /^\/api\/sold$/, async (req, res) => {
  if (!needUser(req, res)) return;
  send(res, 200, {
    sold: db.orders.filter(o => ["escrow", "delivered", "complete"].includes(o.status))
      .sort((a, b) => b.createdAt - a.createdAt).slice(0, 24)
      .map(o => ({ assetId: o.assetId, name: o.name, price: round2(o.price), at: o.createdAt }))
  });
});

/* ---- raffles ---- */
function raffleView(r, uid) {
  return {
    id: r.id, assetId: r.assetId, name: r.name, rap: r.rap ?? null,
    endsAt: r.endsAt, status: r.status, entries: r.entries.length,
    maxEntries: r.maxEntries || 0, joined: uid ? r.entries.includes(uid) : false,
    winner: r.winnerUid ? { uid: r.winnerUid, name: userBy(r.winnerUid)?.username || "(deleted)" } : null,
    note: r.note || "", createdAt: r.createdAt
  };
}
function closeExpiredRaffles() {
  let changed = false;
  for (const r of db.raffles) {
    if (r.status === "open" && r.endsAt <= now()) { r.status = "ended"; changed = true; }
  }
  if (changed) save();
}
route("GET", /^\/api\/raffles$/, async (req, res) => {
  const u = needUser(req, res); if (!u) return;
  closeExpiredRaffles();
  send(res, 200, {
    raffles: db.raffles.filter(r => r.status !== "cancelled")
      .sort((a, b) => (a.status === "open" ? 0 : 1) - (b.status === "open" ? 0 : 1) || b.createdAt - a.createdAt)
      .slice(0, 12).map(r => raffleView(r, u.uid))
  });
});
route("POST", /^\/api\/raffles\/([\w]+)\/join$/, async (req, res, m) => {
  const u = needUser(req, res); if (!u) return;
  closeExpiredRaffles();
  const r = db.raffles.find(x => x.id === m[1]);
  if (!r) return fail(res, 404, "Raffle not found.");
  if (r.status !== "open") return fail(res, 400, "This raffle has closed.");
  if (u.banned) return fail(res, 403, "This account can't enter.");
  if (!u.roblox) return fail(res, 403, "Verify your Roblox account to enter — it keeps alt accounts out.");
  if (r.entries.includes(u.uid)) return fail(res, 409, "You're already entered.");
  if (r.maxEntries && r.entries.length >= r.maxEntries) return fail(res, 400, "This raffle is full.");
  r.entries.push(u.uid);
  save(); send(res, 200, { raffle: raffleView(r, u.uid) });
});

route("POST", /^\/api\/admin\/raffles$/, async (req, res, _m, body) => {
  if (!needAdmin(req, res)) return;
  const assetId = +body.assetId;
  if (!assetId) return fail(res, 400, "Pick an item.");
  const hours = Math.max(0.25, Math.min(720, +body.hours || 24));
  const v = valueOf(assetId);
  const r = {
    id: rid("r_"), assetId, name: String(body.name || v?.name || "Limited item"),
    rap: v?.rap ?? null, note: String(body.note || ""),
    maxEntries: Math.max(0, +body.maxEntries || 0),
    endsAt: now() + hours * 3600000, status: "open", entries: [], winnerUid: null, createdAt: now()
  };
  db.raffles.unshift(r);
  audit("raffle.create", `Raffle for ${r.name}, ends in ${hours}h`, "staff");
  save(); send(res, 200, { raffle: raffleView(r, null) });
});
route("GET", /^\/api\/admin\/raffles$/, async (req, res) => {
  if (!needAdmin(req, res)) return;
  closeExpiredRaffles();
  send(res, 200, {
    raffles: db.raffles.map(r => ({
      ...raffleView(r, null),
      entrants: r.entries.map(uid => ({ uid, name: userBy(uid)?.username || "(deleted)" }))
    }))
  });
});
route("POST", /^\/api\/admin\/raffles\/([\w]+)\/draw$/, async (req, res, m) => {
  if (!needAdmin(req, res)) return;
  const r = db.raffles.find(x => x.id === m[1]);
  if (!r) return fail(res, 404, "Raffle not found.");
  if (r.winnerUid) return fail(res, 400, "A winner was already drawn.");
  if (!r.entries.length) return fail(res, 400, "Nobody entered.");
  /* crypto.randomInt, not Math.random — the draw is uniform and not seedable. */
  r.winnerUid = r.entries[crypto.randomInt(r.entries.length)];
  r.status = "drawn"; r.drawnAt = now();
  const w = userBy(r.winnerUid);
  db.tickets.unshift({
    id: rid("t_"), no: newTicketNo(), uid: r.winnerUid,
    subject: `You won the ${r.name} raffle`, category: "Something else", status: "answered",
    createdAt: now(), updatedAt: now(), unreadStaff: 0, unreadUser: 1,
    messages: [{ from: "support", t: now(), text:
      `Congratulations — you won the ${r.name} raffle out of ${r.entries.length} entries. `
      + `Reply here with your Roblox username and we'll send the trade.` }]
  });
  audit("raffle.draw", `${r.name} won by Seller#${r.winnerUid} (${w?.username}) from ${r.entries.length} entries`, "staff");
  save(); send(res, 200, { winner: { uid: r.winnerUid, name: w?.username || "" }, entries: r.entries.length });
});
route("DELETE", /^\/api\/admin\/raffles\/([\w]+)$/, async (req, res, m) => {
  if (!needAdmin(req, res)) return;
  const r = db.raffles.find(x => x.id === m[1]);
  if (!r) return fail(res, 404, "Raffle not found.");
  db.raffles = db.raffles.filter(x => x.id !== r.id);
  audit("raffle.delete", `Deleted raffle for ${r.name}`, "staff");
  save(); ok(res);
});

/* Accounts a buyer can receive items on. Looked up against Roblox so a typo
   doesn't silently misdirect a trade, but not ownership-verified — a buyer
   choosing their own delivery address doesn't need the phrase-in-bio proof
   that a seller does. */
const MAX_RECEIVING = 8;
route("POST", /^\/api\/account\/receiving$/, async (req, res, _m, body, ip) => {
  const u = needUser(req, res); if (!u) return;
  if (!throttle(ip, "recv", 20, 3600000)) return fail(res, 429, "Slow down a moment.");
  const name = String(body.username || "").trim();
  if (!name) return fail(res, 400, "Enter a Roblox username.");
  u.receivingAccounts = u.receivingAccounts || [];
  if (u.receivingAccounts.length >= MAX_RECEIVING) return fail(res, 400, `You can save up to ${MAX_RECEIVING} accounts.`);
  let found;
  try { found = await robloxByUsername(name); }
  catch (e) { return fail(res, 404, e.message.startsWith("No Roblox") ? e.message : "Couldn't reach Roblox. Try again."); }
  if (u.receivingAccounts.some(a => a.id === found.id)) return fail(res, 409, "That account is already saved.");
  u.receivingAccounts.push({ id: found.id, name: found.name, display: found.display, addedAt: now() });
  save(); send(res, 200, { user: publicUser(u) });
});
route("DELETE", /^\/api\/account\/receiving\/(\d+)$/, async (req, res, m) => {
  const u = needUser(req, res); if (!u) return;
  const before = (u.receivingAccounts || []).length;
  u.receivingAccounts = (u.receivingAccounts || []).filter(a => String(a.id) !== m[1]);
  if (u.receivingAccounts.length === before) return fail(res, 404, "Account not found.");
  save(); send(res, 200, { user: publicUser(u) });
});

/* ---- listings ---- */
route("GET", /^\/api\/listings$/, async (req, res) => {
  if (!needUser(req, res)) return;
  send(res, 200, { listings: db.listings.filter(l => l.status === "active").map(listingView) });
});
route("GET", /^\/api\/listings\/mine$/, async (req, res) => {
  const u = needUser(req, res); if (!u) return;
  send(res, 200, { listings: db.listings.filter(l => l.sellerUid === u.uid).map(listingView) });
});
route("POST", /^\/api\/listings$/, async (req, res, _m, body) => {
  const u = needUser(req, res); if (!u) return;
  if (S("maintenance") || !S("listingsOpen")) return fail(res, 503, "Listing is paused right now.");
  if (u.banned) return fail(res, 403, "This account can't list items.");
  if (!u.roblox) return fail(res, 403, "Verify your Roblox account first.");
  const price = round2(+body.price), uaid = String(body.uaid || "");
  if (!(price > 0)) return fail(res, 400, "Set a price above $0.");
  if (price > 100000) return fail(res, 400, "That price is too high.");
  if (db.listings.some(l => l.uaid === uaid && l.status === "active")) return fail(res, 409, "That copy is already listed.");
  const paymentMethods = Array.isArray(body.paymentMethods)
    ? body.paymentMethods.filter(m => PAYMENT_METHODS.includes(m)) : [];
  if (!paymentMethods.length) return fail(res, 400, "Pick at least one payment method you'll accept.");
  let owned;
  try { owned = await robloxCollectibles(u.roblox.id); }
  catch { return fail(res, 502, "Couldn't confirm ownership with Roblox. Try again shortly."); }
  const copy = owned.find(c => c.uaid === uaid);
  if (!copy) return fail(res, 403, "That item isn't in your Roblox inventory.");
  const l = {
    id: rid("l_"), assetId: copy.assetId, uaid, serial: copy.serial, name: copy.name, rap: copy.rap,
    price, paymentMethods, warrantyHours: S("warrantyHours"), sellerUid: u.uid, status: "active",
    featured: false, createdAt: now()
  };
  db.listings.unshift(l);
  audit("listing.create", `Seller#${u.uid} listed ${copy.name} at ${money(price)}`, u.username);
  save();
  send(res, 200, { listing: listingView(l) });
});
route("PATCH", /^\/api\/listings\/([\w]+)$/, async (req, res, m, body) => {
  const u = needUser(req, res); if (!u) return;
  const l = db.listings.find(x => x.id === m[1]);
  if (!l || l.sellerUid !== u.uid) return fail(res, 404, "Listing not found.");
  if (body.price !== undefined) {
    const p = round2(+body.price);
    if (!(p > 0)) return fail(res, 400, "Set a price above $0.");
    l.price = p;
  }
  save(); ok(res);
});
route("DELETE", /^\/api\/listings\/([\w]+)$/, async (req, res, m) => {
  const u = needUser(req, res); if (!u) return;
  const l = db.listings.find(x => x.id === m[1]);
  if (!l || l.sellerUid !== u.uid) return fail(res, 404, "Listing not found.");
  l.status = "removed"; save(); ok(res);
});

/* ---- orders ---- */
route("POST", /^\/api\/orders$/, async (req, res, _m, body) => {
  const u = needUser(req, res); if (!u) return;
  if (S("maintenance")) return fail(res, 503, "The site is in maintenance mode.");
  const l = db.listings.find(x => x.id === body.listingId);
  if (!l || l.status !== "active") return fail(res, 404, "That listing is no longer available.");
  if (l.sellerUid === u.uid) return fail(res, 400, "You can't buy your own listing.");
  if (u.buyerBalance < l.price) return fail(res, 402, "Not enough buyer balance.");
  const receiving = (u.receivingAccounts || []).find(a => String(a.id) === String(body.receivingId));
  if (!receiving) return fail(res, 400, "Pick which Roblox account should receive this item.");
  const allowed = (Array.isArray(l.paymentMethods) && l.paymentMethods.length) ? l.paymentMethods : PAYMENT_METHODS;
  const paymentMethod = String(body.paymentMethod || "");
  if (!allowed.includes(paymentMethod)) return fail(res, 400, "Pick a payment method the seller accepts.");
  u.buyerBalance = round2(u.buyerBalance - l.price);
  l.status = "sold";
  const fee = round2(l.price * S("commissionPct") / 100);
  const o = {
    id: rid("o_"), listingId: l.id, assetId: l.assetId, uaid: l.uaid, name: l.name,
    serial: l.serial ?? null, house: !!l.house,
    receiving: { id: receiving.id, name: receiving.name }, paymentMethod,
    buyerUid: u.uid, sellerUid: l.sellerUid, price: l.price, fee, payout: round2(l.price - fee),
    warrantyHours: l.warrantyHours ?? S("warrantyHours"), status: "escrow", createdAt: now()
  };
  db.orders.unshift(o);
  audit("order.create", `Seller#${u.uid} bought ${l.name} for ${money(l.price)} from Seller#${l.sellerUid}`, u.username);
  save();
  send(res, 200, { order: orderView(o, u.uid) });
});
route("GET", /^\/api\/orders$/, async (req, res) => {
  const u = needUser(req, res); if (!u) return;
  send(res, 200, {
    bought: db.orders.filter(o => o.buyerUid === u.uid).map(o => orderView(o, u.uid)),
    sold: db.orders.filter(o => o.sellerUid === u.uid).map(o => orderView(o, u.uid))
  });
});
route("POST", /^\/api\/orders\/([\w]+)\/delivered$/, async (req, res, m) => {
  const u = needUser(req, res); if (!u) return;
  const o = db.orders.find(x => x.id === m[1]);
  if (!o || o.sellerUid !== u.uid) return fail(res, 404, "Order not found.");
  if (o.status !== "escrow") return fail(res, 400, "This order isn't in escrow.");
  o.status = "delivered"; o.deliveredAt = now(); save(); ok(res);
});
function completeOrder(o) {
  const s = userBy(o.sellerUid);
  if (s) s.sellerBalance = round2(s.sellerBalance + o.payout);
  o.status = "complete"; o.completedAt = now();
  o.warrantyEnds = now() + (o.warrantyHours || 48) * 3600000;
}
function refundOrder(o, reason) {
  const b = userBy(o.buyerUid);
  if (b) b.buyerBalance = round2(b.buyerBalance + o.price);
  if (o.status === "complete") {
    const s = userBy(o.sellerUid);
    if (s) s.sellerBalance = round2(s.sellerBalance - o.payout);
  }
  o.status = "refunded"; o.refundedAt = now(); o.refundReason = reason || "";
}
route("POST", /^\/api\/orders\/([\w]+)\/confirm$/, async (req, res, m) => {
  const u = needUser(req, res); if (!u) return;
  const o = db.orders.find(x => x.id === m[1]);
  if (!o || o.buyerUid !== u.uid) return fail(res, 404, "Order not found.");
  if (!["escrow", "delivered"].includes(o.status)) return fail(res, 400, "Nothing to confirm.");
  completeOrder(o);
  audit("order.complete", `Seller#${u.uid} confirmed ${o.name}; ${money(o.payout)} released`, u.username);
  save(); ok(res);
});
route("POST", /^\/api\/orders\/([\w]+)\/claim$/, async (req, res, m, body) => {
  const u = needUser(req, res); if (!u) return;
  const o = db.orders.find(x => x.id === m[1]);
  if (!o || o.buyerUid !== u.uid) return fail(res, 404, "Order not found.");
  if (o.status !== "complete") return fail(res, 400, "The warranty starts once you confirm delivery.");
  if (now() > (o.warrantyEnds || 0)) return fail(res, 400, "The warranty window on this order has closed.");
  if (db.claims.some(c => c.orderId === o.id && c.status === "open")) return fail(res, 409, "You already have an open claim on this order.");
  const reason = String(body.reason || "").trim();
  if (reason.length < 10) return fail(res, 400, "Tell us what went wrong, in a sentence or two.");
  db.claims.unshift({ id: rid("c_"), orderId: o.id, uid: u.uid, reason, status: "open", createdAt: now() });
  /* a claim also opens a ticket so the conversation lives in one place */
  const t = {
    id: rid("t_"), no: newTicketNo(), uid: u.uid, subject: `Warranty claim — ${o.name}`,
    category: "Warranty claim", status: "open", createdAt: now(), updatedAt: now(),
    unreadStaff: 1, unreadUser: 0,
    messages: [{ from: "user", text: reason, t: now() }]
  };
  db.tickets.unshift(t);
  audit("claim.open", `Seller#${u.uid} opened a warranty claim on ${o.name}`, u.username);
  save(); send(res, 200, { ticket: t.no });
});

/* ---- balances + withdrawals ---- */
route("POST", /^\/api\/balance\/transfer$/, async (req, res, _m, body) => {
  const u = needUser(req, res); if (!u) return;
  const amount = round2(+body.amount);
  if (!(amount > 0)) return fail(res, 400, "Enter an amount.");
  if (body.direction === "s2b") {
    if (amount > u.sellerBalance) return fail(res, 400, "Not enough seller balance.");
    u.sellerBalance = round2(u.sellerBalance - amount); u.buyerBalance = round2(u.buyerBalance + amount);
  } else {
    if (amount > u.buyerBalance) return fail(res, 400, "Not enough buyer balance.");
    u.buyerBalance = round2(u.buyerBalance - amount); u.sellerBalance = round2(u.sellerBalance + amount);
  }
  save(); send(res, 200, { user: publicUser(u) });
});
const METHODS = ["Crypto", "PayPal", "Bank transfer", "Cash App"];
route("POST", /^\/api\/withdrawals$/, async (req, res, _m, body) => {
  const u = needUser(req, res); if (!u) return;
  const amount = round2(+body.amount);
  const source = body.source === "buyer" ? "buyer" : "seller";
  const method = METHODS.includes(body.method) ? body.method : null;
  const dest = String(body.dest || "").trim();
  if (!method) return fail(res, 400, "Pick a payout method.");
  if (!(amount > 0)) return fail(res, 400, "Enter an amount.");
  if (amount < S("minWithdrawal")) return fail(res, 400, `Minimum withdrawal is ${money(S("minWithdrawal"))}.`);
  const bal = source === "buyer" ? u.buyerBalance : u.sellerBalance;
  if (amount > bal) return fail(res, 400, `That's more than your ${source} balance.`);
  if (dest.length < 4) return fail(res, 400, "Enter where the money should go.");
  if (source === "buyer") u.buyerBalance = round2(u.buyerBalance - amount);
  else u.sellerBalance = round2(u.sellerBalance - amount);
  db.withdrawals.unshift({ id: rid("w_"), uid: u.uid, source, amount, method, dest, status: "pending", createdAt: now() });
  audit("withdrawal.request", `Seller#${u.uid} requested ${money(amount)} via ${method}`, u.username);
  save(); send(res, 200, { user: publicUser(u) });
});
route("GET", /^\/api\/withdrawals$/, async (req, res) => {
  const u = needUser(req, res); if (!u) return;
  send(res, 200, { withdrawals: db.withdrawals.filter(w => w.uid === u.uid) });
});

/* ---- tickets ---- */
const CATEGORIES = ["Payment or withdrawal", "Order or delivery", "Warranty claim",
  "Roblox verification", "Account access", "Something else"];
route("GET", /^\/api\/tickets$/, async (req, res) => {
  const u = needUser(req, res); if (!u) return;
  send(res, 200, {
    categories: CATEGORIES,
    tickets: db.tickets.filter(t => t.uid === u.uid)
      .sort((a, b) => b.updatedAt - a.updatedAt)
      .map(t => ({ ...ticketView(t), messages: undefined, last: t.messages.at(-1)?.text || "" }))
  });
});
route("POST", /^\/api\/tickets$/, async (req, res, _m, body) => {
  const u = needUser(req, res); if (!u) return;
  const subject = String(body.subject || "").trim();
  const text = String(body.text || "").trim();
  const category = CATEGORIES.includes(body.category) ? body.category : "Something else";
  if (subject.length < 4) return fail(res, 400, "Give your ticket a short subject.");
  if (text.length < 5) return fail(res, 400, "Describe the problem so we can help.");
  if (db.tickets.filter(t => t.uid === u.uid && t.status !== "closed").length >= 5)
    return fail(res, 429, "You already have 5 open tickets. Use one of those instead.");
  const t = {
    id: rid("t_"), no: newTicketNo(), uid: u.uid, subject, category, status: "open",
    createdAt: now(), updatedAt: now(), unreadStaff: 1, unreadUser: 0,
    messages: [{ from: "user", text, t: now() }]
  };
  db.tickets.unshift(t);
  save(); send(res, 200, { ticket: ticketView(t) });
});
route("GET", /^\/api\/tickets\/([\w-]+)$/, async (req, res, m) => {
  const u = needUser(req, res); if (!u) return;
  const t = db.tickets.find(x => x.no === m[1] && x.uid === u.uid);
  if (!t) return fail(res, 404, "Ticket not found.");
  t.unreadUser = 0; save();
  send(res, 200, { ticket: ticketView(t) });
});
route("POST", /^\/api\/tickets\/([\w-]+)\/reply$/, async (req, res, m, body) => {
  const u = needUser(req, res); if (!u) return;
  const t = db.tickets.find(x => x.no === m[1] && x.uid === u.uid);
  if (!t) return fail(res, 404, "Ticket not found.");
  if (t.status === "closed") return fail(res, 400, "This ticket is closed. Open a new one.");
  const text = String(body.text || "").trim();
  if (!text) return fail(res, 400, "Type a message.");
  t.messages.push({ from: "user", text, t: now() });
  t.updatedAt = now(); t.unreadStaff = 1; t.status = "open";
  save(); send(res, 200, { ticket: ticketView(t) });
});
route("POST", /^\/api\/tickets\/([\w-]+)\/close$/, async (req, res, m) => {
  const u = needUser(req, res); if (!u) return;
  const t = db.tickets.find(x => x.no === m[1] && x.uid === u.uid);
  if (!t) return fail(res, 404, "Ticket not found.");
  t.status = "closed"; t.updatedAt = now(); save(); ok(res);
});

/* ---- staff ---- */
route("POST", /^\/api\/admin\/login$/, async (req, res, _m, body, ip) => {
  if (!throttle(ip, "adminlogin", 8, 1800000)) return fail(res, 429, "Too many attempts.");
  if (sha256(String(body.user || "").trim()) !== ADMIN.user || sha256(String(body.password || "")) !== ADMIN.pass) {
    audit("admin.failed", `Failed staff login from ${ip}`, "unknown"); save();
    return fail(res, 401, "Incorrect credentials.");
  }
  const s = getSession(req);
  let token;
  if (s) { db.sessions[s.token].admin = true; token = s.token; }
  else token = makeSession(null, true);
  audit("admin.login", "Staff session opened", "staff"); save();
  send(res, 200, { ok: true }, { "Set-Cookie": cookieFor(token) });
});
route("POST", /^\/api\/admin\/logout$/, async (req, res) => {
  const s = getSession(req);
  if (s) { db.sessions[s.token].admin = false; audit("admin.logout", "Staff session locked", "staff"); save(); }
  ok(res);
});

route("GET", /^\/api\/admin\/overview$/, async (req, res) => {
  if (!needAdmin(req, res)) return;
  send(res, 200, {
    users: db.users.length,
    verified: db.users.filter(u => u.verified).length,
    suspended: db.users.filter(u => u.banned).length,
    robloxLinked: db.users.filter(u => u.roblox).length,
    listings: db.listings.filter(l => l.status === "active").length,
    listingsAll: db.listings.length,
    escrow: round2(db.orders.filter(o => o.status === "escrow").reduce((s, o) => s + o.price, 0)),
    openOrders: db.orders.filter(o => o.status === "escrow").length,
    revenue: round2(db.orders.filter(o => o.status === "complete").reduce((s, o) => s + o.fee, 0)),
    liabilities: round2(db.users.reduce((s, u) => s + u.buyerBalance + u.sellerBalance, 0)),
    pendingPayouts: db.withdrawals.filter(w => w.status === "pending").length,
    pendingPayoutTotal: round2(db.withdrawals.filter(w => w.status === "pending").reduce((s, w) => s + w.amount, 0)),
    openClaims: db.claims.filter(c => c.status === "open").length,
    openTickets: db.tickets.filter(t => t.status !== "closed").length,
    audit: db.audit.slice(0, 15)
  });
});

route("GET", /^\/api\/admin\/users$/, async (req, res) => {
  if (!needAdmin(req, res)) return;
  send(res, 200, { users: db.users.map(adminUser) });
});
route("GET", /^\/api\/admin\/users\/(\d+)$/, async (req, res, m) => {
  if (!needAdmin(req, res)) return;
  const u = userBy(m[1]); if (!u) return fail(res, 404, "User not found.");
  send(res, 200, {
    user: adminUser(u),
    listings: db.listings.filter(l => l.sellerUid === u.uid),
    orders: db.orders.filter(o => o.buyerUid === u.uid || o.sellerUid === u.uid),
    withdrawals: db.withdrawals.filter(w => w.uid === u.uid),
    tickets: db.tickets.filter(t => t.uid === u.uid).length
  });
});
route("PATCH", /^\/api\/admin\/users\/(\d+)$/, async (req, res, m, body) => {
  if (!needAdmin(req, res)) return;
  const u = userBy(m[1]); if (!u) return fail(res, 404, "User not found.");
  const ch = [];
  if (body.username && body.username !== u.username) {
    if (db.users.some(x => x.uid !== u.uid && x.username.toLowerCase() === String(body.username).toLowerCase()))
      return fail(res, 409, "That username is taken.");
    ch.push(`username ${u.username}→${body.username}`); u.username = String(body.username).trim();
  }
  if (body.email !== undefined && body.email !== u.email) { ch.push("email updated"); u.email = String(body.email).trim().toLowerCase(); }
  if (body.buyerBalance !== undefined) { ch.push(`buyer ${money(u.buyerBalance)}→${money(+body.buyerBalance)}`); u.buyerBalance = round2(+body.buyerBalance); }
  if (body.sellerBalance !== undefined) { ch.push(`seller ${money(u.sellerBalance)}→${money(+body.sellerBalance)}`); u.sellerBalance = round2(+body.sellerBalance); }
  if (body.verified !== undefined && !!body.verified !== !!u.verified) { u.verified = !!body.verified; ch.push(u.verified ? "verified" : "unverified"); }
  if (body.banned !== undefined && !!body.banned !== !!u.banned) {
    u.banned = !!body.banned; ch.push(u.banned ? "suspended" : "restored");
    if (u.banned) for (const [tok, s] of Object.entries(db.sessions)) if (s.uid === u.uid) delete db.sessions[tok];
  }
  if (body.notes !== undefined) u.notes = String(body.notes);
  if (body.clearRoblox) { u.roblox = null; u.pendingRoblox = null; ch.push("Roblox link cleared"); }
  audit("user.edit", `Seller#${u.uid}: ${ch.join(", ") || "details updated"}`, "staff");
  save(); send(res, 200, { user: adminUser(u) });
});
route("POST", /^\/api\/admin\/users\/(\d+)\/balance$/, async (req, res, m, body) => {
  if (!needAdmin(req, res)) return;
  const u = userBy(m[1]); if (!u) return fail(res, 404, "User not found.");
  const amount = round2(+body.amount);
  if (!amount) return fail(res, 400, "Enter an amount.");
  const which = body.which === "seller" ? "sellerBalance" : "buyerBalance";
  u[which] = round2(u[which] + amount);
  audit("balance.adjust", `${amount >= 0 ? "+" : ""}${money(amount)} to Seller#${u.uid} ${body.which || "buyer"} balance — ${body.reason || "no reason given"}`, "staff");
  save(); send(res, 200, { user: adminUser(u) });
});
route("POST", /^\/api\/admin\/users\/(\d+)\/password$/, async (req, res, m, body) => {
  if (!needAdmin(req, res)) return;
  const u = userBy(m[1]); if (!u) return fail(res, 404, "User not found.");
  const temp = String(body.password || "").length >= 8 ? String(body.password) : "bs-" + crypto.randomBytes(5).toString("hex");
  u.pass = hashPassword(temp);
  for (const [tok, s] of Object.entries(db.sessions)) if (s.uid === u.uid) delete db.sessions[tok];
  audit("user.password.reset", `Support reset the password for Seller#${u.uid} (${u.username})`, "staff");
  save(); send(res, 200, { password: temp });
});
route("POST", /^\/api\/admin\/users\/(\d+)\/impersonate$/, async (req, res, m) => {
  if (!needAdmin(req, res)) return;
  const u = userBy(m[1]); if (!u) return fail(res, 404, "User not found.");
  db.sessions[getSession(req).token].uid = u.uid;
  audit("user.impersonate", `Staff signed in as Seller#${u.uid}`, "staff");
  save(); send(res, 200, { user: publicUser(u) });
});
route("DELETE", /^\/api\/admin\/users\/(\d+)$/, async (req, res, m) => {
  if (!needAdmin(req, res)) return;
  const u = userBy(m[1]); if (!u) return fail(res, 404, "User not found.");
  db.users = db.users.filter(x => x.uid !== u.uid);
  db.listings = db.listings.filter(l => l.sellerUid !== u.uid);
  db.tickets = db.tickets.filter(t => t.uid !== u.uid);
  for (const [tok, s] of Object.entries(db.sessions)) if (s.uid === u.uid) delete db.sessions[tok];
  audit("user.delete", `Deleted Seller#${u.uid} (${u.username})`, "staff");
  save(); ok(res);
});
route("POST", /^\/api\/admin\/users$/, async (req, res, _m, body) => {
  if (!needAdmin(req, res)) return;
  const username = String(body.username || "").trim(), password = String(body.password || "");
  if (username.length < 3 || password.length < 8) return fail(res, 400, "Username 3+ chars, password 8+ chars.");
  if (db.users.some(u => u.username.toLowerCase() === username.toLowerCase())) return fail(res, 409, "Username taken.");
  const u = {
    uid: newUid(), username, email: String(body.email || "").trim().toLowerCase(), pass: hashPassword(password),
    buyerBalance: round2(+body.buyerBalance || 0), sellerBalance: round2(+body.sellerBalance || 0),
    verified: false, banned: false, roblox: null, pendingRoblox: null,
    createdAt: now(), lastLogin: null, loginCount: 0, notes: "Created by support"
  };
  db.users.push(u);
  audit("user.create", `Created Seller#${u.uid} (${username})`, "staff");
  save(); send(res, 200, { user: adminUser(u) });
});

route("GET", /^\/api\/admin\/listings$/, async (req, res) => {
  if (!needAdmin(req, res)) return;
  send(res, 200, { listings: db.listings.map(l => ({ ...l, sellerVerified: !!userBy(l.sellerUid)?.verified })) });
});
route("PATCH", /^\/api\/admin\/listings\/([\w]+)$/, async (req, res, m, body) => {
  if (!needAdmin(req, res)) return;
  const l = db.listings.find(x => x.id === m[1]); if (!l) return fail(res, 404, "Listing not found.");
  if (body.price !== undefined) l.price = round2(+body.price);
  if (body.status) l.status = body.status;
  if (body.featured !== undefined) l.featured = !!body.featured;
  audit("listing.admin", `${l.name}: ${money(l.price)}, ${l.status}${l.featured ? ", featured" : ""}`, "staff");
  save(); ok(res);
});
route("DELETE", /^\/api\/admin\/listings\/([\w]+)$/, async (req, res, m) => {
  if (!needAdmin(req, res)) return;
  const l = db.listings.find(x => x.id === m[1]); if (!l) return fail(res, 404, "Listing not found.");
  db.listings = db.listings.filter(x => x.id !== l.id);
  audit("listing.delete", `Deleted listing "${l.name}"`, "staff"); save(); ok(res);
});
/* Search every Roblox limited by name or asset id. Read-only lookup. */
route("GET", /^\/api\/admin\/limiteds$/, async (req, res, _m, _b, _ip, url) => {
  if (!needAdmin(req, res)) return;
  const q = String(url.searchParams.get("q") || "").trim().toLowerCase();
  const min = +url.searchParams.get("min") || 0;
  const max = +url.searchParams.get("max") || Infinity;
  const out = [];
  for (const [id, v] of valueIndex) {
    const worth = v.value > 0 ? v.value : v.rap;
    if (worth < min || worth > max) continue;
    if (q && !v.name.toLowerCase().includes(q) && !(v.acr || "").toLowerCase().includes(q) && String(id) !== q) continue;
    out.push({ assetId: id, name: v.name, acr: v.acr, rap: v.rap, value: v.value, demand: v.demand, projected: v.projected });
  }
  out.sort((a, b) => (b.value > 0 ? b.value : b.rap) - (a.value > 0 ? a.value : a.rap));
  send(res, 200, { total: out.length, items: out.slice(0, 60), indexed: valueIndex.size });
});

/* House listings: stock BloxSwap itself holds. Sold under the house account and
   badged as such, so buyers always know who they're buying from. The Roblox
   ownership check is skipped here because there is no seller inventory to check —
   only list items you can actually deliver. */
function houseAccount() {
  let h = db.users.find(u => u.house);
  if (!h) {
    h = {
      uid: newUid(), username: "BloxSwap", email: "", pass: hashPassword(crypto.randomBytes(24).toString("hex")),
      buyerBalance: 0, sellerBalance: 0, verified: true, banned: false, house: true,
      roblox: null, pendingRoblox: null, createdAt: now(), lastLogin: null, loginCount: 0,
      notes: "House account — official BloxSwap stock. Cannot be logged into."
    };
    db.users.push(h);
    audit("house.create", `Created house account Seller#${h.uid}`, "staff");
  }
  return h;
}
route("GET", /^\/api\/admin\/house$/, async (req, res) => {
  if (!needAdmin(req, res)) return;
  const h = houseAccount();
  send(res, 200, {
    uid: h.uid, roblox: h.roblox || null,
    listings: db.listings.filter(l => l.sellerUid === h.uid).map(listingView)
  });
});
route("POST", /^\/api\/admin\/house\/roblox$/, async (req, res, _m, body) => {
  if (!needAdmin(req, res)) return;
  const h = houseAccount();
  const name = String(body.username || "").trim();
  if (!name) { h.roblox = null; save(); return ok(res); }
  let found;
  try { found = await robloxByUsername(name); }
  catch (e) { return fail(res, 404, e.message); }
  h.roblox = { id: found.id, name: found.name, display: found.display, linkedAt: now() };
  audit("house.roblox", `House account trades from ${found.name} (${found.id})`, "staff");
  save(); send(res, 200, { roblox: h.roblox });
});
route("POST", /^\/api\/admin\/house\/listings$/, async (req, res, _m, body) => {
  if (!needAdmin(req, res)) return;
  const h = houseAccount();
  if (!h.roblox) return fail(res, 400, "Set the house Roblox account first — buyers need someone to trade with.");
  const assetId = +body.assetId, price = round2(+body.price);
  if (!assetId) return fail(res, 400, "Pick an item.");
  if (!(price > 0)) return fail(res, 400, "Set a price above $0.");
  const v = valueOf(assetId);
  const paymentMethods = Array.isArray(body.paymentMethods)
    ? body.paymentMethods.filter(m => PAYMENT_METHODS.includes(m)) : PAYMENT_METHODS;
  const l = {
    id: rid("l_"), assetId, uaid: "house-" + assetId + "-" + crypto.randomBytes(3).toString("hex"),
    serial: body.serial ? +body.serial : null, name: String(body.name || v?.name || "Limited item"),
    rap: v?.rap ?? null, price, paymentMethods, warrantyHours: S("warrantyHours"), sellerUid: h.uid,
    house: true, status: "active", featured: !!body.featured, createdAt: now()
  };
  db.listings.unshift(l);
  audit("house.listing", `Listed ${l.name} at ${money(price)} as house stock`, "staff");
  save(); send(res, 200, { listing: listingView(l) });
});

route("POST", /^\/api\/admin\/listings\/clear$/, async (req, res, _m, body) => {
  if (!needAdmin(req, res)) return;
  if (body.confirm !== "CLEAR LISTINGS") return fail(res, 400, "Confirmation text didn't match.");
  const n = db.listings.length; db.listings = [];
  audit("listing.clear", `Removed all ${n} listings`, "staff");
  save(); send(res, 200, { removed: n });
});

route("GET", /^\/api\/admin\/orders$/, async (req, res) => {
  if (!needAdmin(req, res)) return; send(res, 200, { orders: db.orders });
});
route("POST", /^\/api\/admin\/orders\/([\w]+)\/(release|refund|delete)$/, async (req, res, m, body) => {
  if (!needAdmin(req, res)) return;
  const o = db.orders.find(x => x.id === m[1]); if (!o) return fail(res, 404, "Order not found.");
  if (m[2] === "release") {
    if (!["escrow", "delivered"].includes(o.status)) return fail(res, 400, "Nothing to release.");
    completeOrder(o); audit("order.release", `Released ${money(o.payout)} on ${o.id.slice(0, 10)}`, "staff");
  } else if (m[2] === "refund") {
    if (o.status === "refunded") return fail(res, 400, "Already refunded.");
    refundOrder(o, body.reason || "Support refund");
    audit("order.refund", `Refunded ${money(o.price)} on ${o.id.slice(0, 10)}`, "staff");
  } else {
    db.orders = db.orders.filter(x => x.id !== o.id);
    audit("order.delete", `Deleted order ${o.id.slice(0, 10)}`, "staff");
  }
  save(); ok(res);
});

route("GET", /^\/api\/admin\/withdrawals$/, async (req, res) => {
  if (!needAdmin(req, res)) return;
  send(res, 200, { withdrawals: db.withdrawals.map(w => ({ ...w, username: userBy(w.uid)?.username || "" })) });
});
route("POST", /^\/api\/admin\/withdrawals\/([\w]+)\/(paid|reject)$/, async (req, res, m, body) => {
  if (!needAdmin(req, res)) return;
  const w = db.withdrawals.find(x => x.id === m[1]); if (!w) return fail(res, 404, "Not found.");
  if (w.status !== "pending") return fail(res, 400, "Already handled.");
  if (m[2] === "paid") {
    w.status = "paid"; w.paidAt = now(); w.reference = String(body.reference || "");
    audit("withdrawal.paid", `Paid ${money(w.amount)} via ${w.method} to Seller#${w.uid}`, "staff");
  } else {
    const u = userBy(w.uid);
    if (u) { if (w.source === "buyer") u.buyerBalance = round2(u.buyerBalance + w.amount); else u.sellerBalance = round2(u.sellerBalance + w.amount); }
    w.status = "rejected";
    audit("withdrawal.reject", `Rejected ${money(w.amount)} for Seller#${w.uid}, funds returned`, "staff");
  }
  save(); ok(res);
});

route("GET", /^\/api\/admin\/claims$/, async (req, res) => {
  if (!needAdmin(req, res)) return;
  send(res, 200, { claims: db.claims.map(c => ({ ...c, order: db.orders.find(o => o.id === c.orderId) || null })) });
});
route("POST", /^\/api\/admin\/claims\/([\w]+)\/(approve|reject)$/, async (req, res, m) => {
  if (!needAdmin(req, res)) return;
  const c = db.claims.find(x => x.id === m[1]); if (!c) return fail(res, 404, "Claim not found.");
  const o = db.orders.find(x => x.id === c.orderId);
  if (m[2] === "approve") {
    if (o && o.status !== "refunded") refundOrder(o, "Warranty claim approved");
    c.status = "approved"; audit("claim.approve", `Approved claim ${c.id.slice(0, 10)}`, "staff");
  } else { c.status = "rejected"; audit("claim.reject", `Rejected claim ${c.id.slice(0, 10)}`, "staff"); }
  save(); ok(res);
});

route("GET", /^\/api\/admin\/tickets$/, async (req, res) => {
  if (!needAdmin(req, res)) return;
  send(res, 200, {
    tickets: db.tickets.sort((a, b) => b.updatedAt - a.updatedAt).map(t => ({
      no: t.no, uid: t.uid, username: userBy(t.uid)?.username || "(deleted)",
      subject: t.subject, category: t.category, status: t.status,
      updatedAt: t.updatedAt, unread: !!t.unreadStaff, last: t.messages.at(-1)?.text || ""
    }))
  });
});
route("GET", /^\/api\/admin\/tickets\/([\w-]+)$/, async (req, res, m) => {
  if (!needAdmin(req, res)) return;
  const t = db.tickets.find(x => x.no === m[1]); if (!t) return fail(res, 404, "Ticket not found.");
  t.unreadStaff = 0; save();
  const u = userBy(t.uid);
  send(res, 200, { ticket: ticketView(t), user: u ? adminUser(u) : null });
});
route("POST", /^\/api\/admin\/tickets\/([\w-]+)\/reply$/, async (req, res, m, body) => {
  if (!needAdmin(req, res)) return;
  const t = db.tickets.find(x => x.no === m[1]); if (!t) return fail(res, 404, "Ticket not found.");
  const text = String(body.text || "").trim();
  if (!text) return fail(res, 400, "Type a message.");
  t.messages.push({ from: "support", text, t: now() });
  t.updatedAt = now(); t.unreadUser = 1; t.unreadStaff = 0;
  if (body.status && ["open", "answered", "resolved", "closed"].includes(body.status)) t.status = body.status;
  else t.status = "answered";
  save(); send(res, 200, { ticket: ticketView(t) });
});
route("POST", /^\/api\/admin\/tickets\/([\w-]+)\/status$/, async (req, res, m, body) => {
  if (!needAdmin(req, res)) return;
  const t = db.tickets.find(x => x.no === m[1]); if (!t) return fail(res, 404, "Ticket not found.");
  if (!["open", "answered", "resolved", "closed"].includes(body.status)) return fail(res, 400, "Unknown status.");
  t.status = body.status; t.updatedAt = now();
  audit("ticket.status", `${t.no} set to ${t.status}`, "staff");
  save(); ok(res);
});
route("DELETE", /^\/api\/admin\/tickets\/([\w-]+)$/, async (req, res, m) => {
  if (!needAdmin(req, res)) return;
  const t = db.tickets.find(x => x.no === m[1]);
  if (!t) return fail(res, 404, "Ticket not found.");
  db.tickets = db.tickets.filter(x => x.no !== t.no);
  audit("ticket.delete", `Deleted ${t.no} "${t.subject}" from Seller#${t.uid}`, "staff");
  save(); ok(res);
});
route("POST", /^\/api\/admin\/tickets\/purge$/, async (req, res, _m, body) => {
  if (!needAdmin(req, res)) return;
  const which = body.which === "all" ? "all" : "closed";
  const before = db.tickets.length;
  db.tickets = which === "all" ? [] : db.tickets.filter(t => !["closed", "resolved"].includes(t.status));
  const n = before - db.tickets.length;
  audit("ticket.purge", `Deleted ${n} ${which === "all" ? "" : "closed/resolved "}tickets`, "staff");
  save(); send(res, 200, { removed: n });
});

route("POST", /^\/api\/admin\/broadcast$/, async (req, res, _m, body) => {
  if (!needAdmin(req, res)) return;
  const text = String(body.text || "").trim();
  const subject = String(body.subject || "Announcement").trim();
  if (!text) return fail(res, 400, "Type a message.");
  for (const u of db.users) {
    db.tickets.unshift({
      id: rid("t_"), no: newTicketNo(), uid: u.uid, subject, category: "Something else",
      status: "answered", createdAt: now(), updatedAt: now(), unreadStaff: 0, unreadUser: 1,
      messages: [{ from: "support", text, t: now() }]
    });
  }
  audit("support.broadcast", `Opened a ticket for all ${db.users.length} accounts`, "staff");
  save(); ok(res);
});

route("GET", /^\/api\/admin\/settings$/, async (req, res) => {
  if (!needAdmin(req, res)) return; send(res, 200, { settings: db.settings });
});
route("PATCH", /^\/api\/admin\/settings$/, async (req, res, _m, body) => {
  if (!needAdmin(req, res)) return;
  for (const k of Object.keys(DEFAULT_SETTINGS)) if (body[k] !== undefined) db.settings[k] = body[k];
  if (body.announce !== undefined) db.settings.announce = body.announce;
  if (body.minDeposit !== undefined) db.settings.minDeposit = Math.max(0, +body.minDeposit || 0);
  if (body.wallets !== undefined && typeof body.wallets === "object") {
    db.settings.wallets = db.settings.wallets || {};
    for (const c of DEPOSIT_COINS) if (body.wallets[c] !== undefined) db.settings.wallets[c] = String(body.wallets[c]).trim();
  }
  db.settings.commissionPct = Math.max(0, Math.min(50, +db.settings.commissionPct || 0));
  db.settings.warrantyHours = Math.max(1, +db.settings.warrantyHours || 48);
  db.settings.minWithdrawal = Math.max(0, +db.settings.minWithdrawal || 0);
  db.settings.brandColor = safeHex(db.settings.brandColor, DEFAULT_SETTINGS.brandColor);
  db.settings.secondaryColor = safeHex(db.settings.secondaryColor, DEFAULT_SETTINGS.secondaryColor);
  db.settings.featuredColor = safeHex(db.settings.featuredColor, DEFAULT_SETTINGS.featuredColor);
  db.settings.verifiedColor = safeHex(db.settings.verifiedColor, DEFAULT_SETTINGS.verifiedColor);
  audit("settings.update", `commission ${db.settings.commissionPct}%, warranty ${db.settings.warrantyHours}h, maintenance ${db.settings.maintenance ? "on" : "off"}`, "staff");
  save(); send(res, 200, { settings: db.settings });
});
route("GET", /^\/api\/admin\/audit$/, async (req, res) => {
  if (!needAdmin(req, res)) return; send(res, 200, { audit: db.audit });
});
route("GET", /^\/api\/admin\/export$/, async (req, res) => {
  if (!needAdmin(req, res)) return;
  const copy = JSON.parse(JSON.stringify(db));
  copy.sessions = {};
  for (const u of copy.users) u.pass = "[redacted]";
  send(res, 200, copy, { "Content-Disposition": `attachment; filename=bloxswap-${new Date().toISOString().slice(0, 10)}.json` });
});
route("POST", /^\/api\/admin\/wipe$/, async (req, res, _m, body) => {
  if (!needAdmin(req, res)) return;
  if (body.confirm !== "WIPE EVERYTHING") return fail(res, 400, "Confirmation text didn't match.");
  const keep = db.sessions;
  db = blank(); db.sessions = keep;
  audit("data.wipe", "All marketplace data wiped", "staff");
  save(); ok(res);
});

/* ---- CRYPTO DEPOSITS ----
   A manual review queue: the user says they've sent crypto to one of our
   published wallet addresses, staff verify the chain and approve, which credits
   buyer balance. No processor keys live in the client, and no balance is created
   until a human approves — a spoofed "paid" call can't mint funds. When you wire
   a real processor (Coinbase Commerce, NOWPayments…) its webhook approves here
   instead of a person. */

const DEPOSIT_COINS = ["Bitcoin (BTC)", "Ethereum (ETH)", "Litecoin (LTC)", "USDT (TRC-20)"];

/* Public-ish: which coins we accept and the addresses to send to. */
route("GET", /^\/api\/deposit\/options$/, async (req, res) => {
  if (!needUser(req, res)) return;
  const wallets = db.settings.wallets || {};
  const coins = DEPOSIT_COINS.filter(c => wallets[c]).map(c => ({ coin: c, address: wallets[c] }));
  send(res, 200, { coins, minDeposit: S("minDeposit") });
});

/* User submits a deposit claim: coin, USD amount they sent, and their tx hash. */
route("POST", /^\/api\/deposit$/, async (req, res, _m, body) => {
  const u = needUser(req, res); if (!u) return;
  const coin = DEPOSIT_COINS.includes(body.coin) ? body.coin : null;
  const amount = round2(+body.amount);
  const txid = String(body.txid || "").trim();
  if (!coin) return fail(res, 400, "Pick a coin.");
  if (!(db.settings.wallets || {})[coin]) return fail(res, 400, "That coin isn't accepted right now.");
  if (!(amount > 0)) return fail(res, 400, "Enter the USD amount you sent.");
  if (amount < S("minDeposit")) return fail(res, 400, `Minimum deposit is ${money(S("minDeposit"))}.`);
  if (txid.length < 6) return fail(res, 400, "Paste the transaction hash so we can verify it on-chain.");
  if (db.deposits.some(d => d.txid === txid && d.status !== "rejected"))
    return fail(res, 409, "That transaction has already been submitted.");
  if (db.deposits.filter(d => d.uid === u.uid && d.status === "pending").length >= 5)
    return fail(res, 429, "You already have 5 deposits under review.");
  const d = {
    id: rid("d_"), uid: u.uid, coin, amount, txid,
    address: db.settings.wallets[coin], status: "pending", createdAt: now()
  };
  db.deposits.unshift(d);
  audit("deposit.request", `Seller#${u.uid} claims ${money(amount)} via ${coin}`, u.username);
  save();
  send(res, 200, { deposit: { id: d.id, coin: d.coin, amount: d.amount, txid: d.txid, status: d.status, createdAt: d.createdAt } });
});

/* User's own deposit history. */
route("GET", /^\/api\/deposit$/, async (req, res) => {
  const u = needUser(req, res); if (!u) return;
  send(res, 200, { deposits: db.deposits.filter(d => d.uid === u.uid)
    .map(d => ({ id: d.id, coin: d.coin, amount: d.amount, txid: d.txid, status: d.status, createdAt: d.createdAt })) });
});

/* Staff: review queue. */
route("GET", /^\/api\/admin\/deposits$/, async (req, res) => {
  if (!needAdmin(req, res)) return;
  send(res, 200, { deposits: db.deposits.map(d => ({ ...d, username: userBy(d.uid)?.username || "(deleted)" })) });
});
route("POST", /^\/api\/admin\/deposits\/([\w]+)\/(approve|reject)$/, async (req, res, m, body) => {
  if (!needAdmin(req, res)) return;
  const d = db.deposits.find(x => x.id === m[1]); if (!d) return fail(res, 404, "Deposit not found.");
  if (d.status !== "pending") return fail(res, 400, "Already handled.");
  if (m[2] === "approve") {
    const u = userBy(d.uid);
    const credit = body.amount !== undefined ? round2(+body.amount) : d.amount;  // staff can adjust to the real received amount
    if (u) u.buyerBalance = round2(u.buyerBalance + credit);
    d.status = "approved"; d.creditedAmount = credit; d.handledAt = now();
    audit("deposit.approve", `Credited ${money(credit)} to Seller#${d.uid} for ${d.coin} deposit ${d.txid.slice(0, 12)}`, "staff");
  } else {
    d.status = "rejected"; d.handledAt = now(); d.rejectReason = String(body.reason || "");
    audit("deposit.reject", `Rejected ${d.coin} deposit from Seller#${d.uid}`, "staff");
  }
  save(); ok(res);
});

/* ---- MORE STAFF TOOLS ---- */

/* Dashboard analytics: volume, top items, top sellers, recent activity totals. */
route("GET", /^\/api\/admin\/stats$/, async (req, res) => {
  if (!needAdmin(req, res)) return;
  const complete = db.orders.filter(o => o.status === "complete");
  const gmv = complete.reduce((s, o) => s + o.price, 0);
  const byDay = {};
  for (const o of complete) {
    const day = new Date(o.completedAt || o.createdAt).toISOString().slice(0, 10);
    byDay[day] = (byDay[day] || 0) + o.price;
  }
  const days = Object.entries(byDay).sort().slice(-14).map(([d, v]) => ({ d, v: round2(v) }));
  const itemCounts = {};
  for (const o of complete) itemCounts[o.name] = (itemCounts[o.name] || 0) + 1;
  const topItems = Object.entries(itemCounts).sort((a, b) => b[1] - a[1]).slice(0, 8).map(([name, n]) => ({ name, n }));
  const sellerVol = {};
  for (const o of complete) sellerVol[o.sellerUid] = (sellerVol[o.sellerUid] || 0) + o.price;
  const topSellers = Object.entries(sellerVol).sort((a, b) => b[1] - a[1]).slice(0, 8)
    .map(([uid, v]) => ({ uid, name: userBy(uid)?.username || "(deleted)", v: round2(v) }));
  send(res, 200, {
    gmv: round2(gmv), completedCount: complete.length,
    avgOrder: complete.length ? round2(gmv / complete.length) : 0,
    refunded: db.orders.filter(o => o.status === "refunded").length,
    days, topItems, topSellers,
    newUsers7d: db.users.filter(u => now() - u.createdAt < 7 * 864e5).length,
    activeUsers7d: db.users.filter(u => u.lastLogin && now() - u.lastLogin < 7 * 864e5).length,
    totalRaffles: db.raffles.length, totalTickets: db.tickets.length
  });
});

/* Global search across users, listings, orders, tickets in one call. */
route("GET", /^\/api\/admin\/search$/, async (req, res, _m, _b, _ip, url) => {
  if (!needAdmin(req, res)) return;
  const q = String(url.searchParams.get("q") || "").trim().toLowerCase();
  if (!q) return send(res, 200, { users: [], listings: [], orders: [], tickets: [] });
  const users = db.users.filter(u => u.username.toLowerCase().includes(q) || (u.email || "").includes(q)
    || u.uid.includes(q) || (u.roblox?.name || "").toLowerCase().includes(q)).slice(0, 8).map(adminUser);
  const listings = db.listings.filter(l => l.name.toLowerCase().includes(q) || l.id.includes(q))
    .slice(0, 8).map(l => ({ id: l.id, name: l.name, price: round2(l.price), status: l.status, sellerUid: l.sellerUid }));
  const orders = db.orders.filter(o => o.name.toLowerCase().includes(q) || o.id.includes(q)
    || String(o.buyerUid).includes(q) || String(o.sellerUid).includes(q))
    .slice(0, 8).map(o => ({ id: o.id, name: o.name, price: round2(o.price), status: o.status, buyerUid: o.buyerUid, sellerUid: o.sellerUid }));
  const tickets = db.tickets.filter(t => t.subject.toLowerCase().includes(q) || t.no.toLowerCase().includes(q))
    .slice(0, 8).map(t => ({ no: t.no, subject: t.subject, status: t.status, uid: t.uid }));
  send(res, 200, { users, listings, orders, tickets });
});

/* Credit or deduct every account at once (event payouts, apology credits, etc). */
route("POST", /^\/api\/admin\/credit-all$/, async (req, res, _m, body) => {
  if (!needAdmin(req, res)) return;
  const amount = round2(+body.amount);
  if (!amount) return fail(res, 400, "Enter an amount.");
  const which = body.which === "seller" ? "sellerBalance" : "buyerBalance";
  const onlyVerified = !!body.onlyVerified;
  let n = 0;
  for (const u of db.users) {
    if (u.house) continue;
    if (onlyVerified && !u.verified) continue;
    u[which] = round2(u[which] + amount);
    n++;
  }
  audit("balance.credit-all", `${amount >= 0 ? "+" : ""}${money(amount)} to ${which} of ${n} accounts${onlyVerified ? " (verified only)" : ""} — ${body.reason || "no reason"}`, "staff");
  save(); send(res, 200, { affected: n });
});

/* Bulk verify / suspend / restore by a list of user IDs. */
route("POST", /^\/api\/admin\/users\/bulk$/, async (req, res, _m, body) => {
  if (!needAdmin(req, res)) return;
  const ids = Array.isArray(body.uids) ? body.uids.map(String) : [];
  const action = body.action;
  if (!ids.length) return fail(res, 400, "No accounts selected.");
  let n = 0;
  for (const u of db.users) {
    if (!ids.includes(u.uid) || u.house) continue;
    if (action === "verify") u.verified = true;
    else if (action === "unverify") u.verified = false;
    else if (action === "suspend") { u.banned = true; for (const [tok, ses] of Object.entries(db.sessions)) if (ses.uid === u.uid) delete db.sessions[tok]; }
    else if (action === "restore") u.banned = false;
    else return fail(res, 400, "Unknown action.");
    n++;
  }
  audit("user.bulk", `${action} on ${n} accounts`, "staff");
  save(); send(res, 200, { affected: n });
});

/* A pinned announcement banner separate from the plain site notice —
   dismissible per user, styled, with a level. */
route("POST", /^\/api\/admin\/announce$/, async (req, res, _m, body) => {
  if (!needAdmin(req, res)) return;
  const text = String(body.text || "").trim();
  const level = ["info", "warn", "good"].includes(body.level) ? body.level : "info";
  db.settings.announce = text ? { text, level, at: now() } : null;
  audit("settings.announce", text ? `Set ${level} announcement` : "Cleared announcement", "staff");
  save(); send(res, 200, { announce: db.settings.announce });
});

/* Force-close a raffle early (turns "open" into "ended" so it can be drawn now). */
route("POST", /^\/api\/admin\/raffles\/([\w]+)\/close$/, async (req, res, m) => {
  if (!needAdmin(req, res)) return;
  const r = db.raffles.find(x => x.id === m[1]); if (!r) return fail(res, 404, "Raffle not found.");
  if (r.status !== "open") return fail(res, 400, "Raffle isn't open.");
  r.status = "ended"; r.endsAt = now();
  audit("raffle.close", `Closed ${r.name} early with ${r.entries.length} entries`, "staff");
  save(); send(res, 200, { raffle: raffleView(r, null) });
});

/* Add an internal note to any order (for dispute tracking). */
route("POST", /^\/api\/admin\/orders\/([\w]+)\/note$/, async (req, res, m, body) => {
  if (!needAdmin(req, res)) return;
  const o = db.orders.find(x => x.id === m[1]); if (!o) return fail(res, 404, "Order not found.");
  o.staffNote = String(body.note || "").slice(0, 500);
  audit("order.note", `Noted order ${o.id.slice(0, 10)}`, "staff");
  save(); ok(res);
});

/* Full session list — who's logged in right now, with the ability to kick them. */
route("GET", /^\/api\/admin\/sessions$/, async (req, res) => {
  if (!needAdmin(req, res)) return;
  const list = Object.entries(db.sessions).map(([tok, ssn]) => ({
    token: tok.slice(0, 10), uid: ssn.uid, admin: !!ssn.admin,
    username: ssn.uid ? (userBy(ssn.uid)?.username || "(deleted)") : (ssn.admin ? "staff-only" : "?"),
    created: ssn.created, expires: ssn.expires
  })).sort((a, b) => b.created - a.created);
  send(res, 200, { sessions: list, total: Object.keys(db.sessions).length });
});
route("POST", /^\/api\/admin\/sessions\/kick-all$/, async (req, res) => {
  if (!needAdmin(req, res)) return;
  const me = getSession(req).token;
  const before = Object.keys(db.sessions).length;
  db.sessions = { [me]: db.sessions[me] };
  audit("session.kick-all", `Ended ${before - 1} sessions`, "staff");
  save(); send(res, 200, { ended: before - 1 });
});

/* Feature or unfeature a listing by id — quick toggle used from several places. */
route("POST", /^\/api\/admin\/feature\/([\w]+)$/, async (req, res, m, body) => {
  if (!needAdmin(req, res)) return;
  const l = db.listings.find(x => x.id === m[1]); if (!l) return fail(res, 404, "Listing not found.");
  l.featured = !!body.featured;
  audit("listing.feature", `${l.featured ? "Featured" : "Unfeatured"} ${l.name}`, "staff");
  save(); ok(res);
});

/* ===========================================================================
   Server
   =========================================================================== */
http.createServer(async (req, res) => {
  const url = new URL(req.url, "http://x");
  const ip = (req.headers["x-forwarded-for"] || "").split(",")[0].trim() || req.socket.remoteAddress || "?";
  if (!url.pathname.startsWith("/api/")) return serveStatic(res, url.pathname);
  for (const r of routes) {
    if (r.method !== req.method) continue;
    const m = url.pathname.match(r.pattern);
    if (!m) continue;
    try {
      const body = ["POST", "PATCH", "PUT"].includes(req.method) ? await readBody(req) : {};
      return await r.handler(req, res, m, body, ip, url);
    } catch (e) {
      console.error(req.method, url.pathname, e.message);
      if (!res.headersSent) return fail(res, 500, "Something went wrong on our side.");
      return;
    }
  }
  fail(res, 404, "No such endpoint.");
}).listen(PORT, () => {
  console.log(`\n  BloxSwap  →  http://localhost:${PORT}`);
  console.log(`  Data file →  ${DATA_FILE}`);
  console.log(`  Accounts  →  ${db.users.length}   Listings → ${db.listings.length}\n`);
});