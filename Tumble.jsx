// Tumble - a tiny 2D rigid body engine.
// Written in ES3 style (no let/const/arrow functions) so it runs inside
// After Effects' ExtendScript as well as in Node for testing.
// Coordinates: pixels, y axis points DOWN (same as After Effects).

var Tumble = (function () {

  function World(opts) {
    opts = opts || {};
    this.gravityY = opts.gravity !== undefined ? opts.gravity : 980; // px/s^2
    this.gravityX = 0;
    this.substeps = opts.substeps || 8;
    this.iterations = opts.iterations || 6;
    this.bodies = [];
    this.joints = [];
    this.waters = [];
    this.explosions = [];
    this.portals = [];
    this.wrapBounds = null;
    this.triggers = [];
    this.time = 0;
    this.subTime = 0;
    // Contact log: when recordContacts is on, every NEW touch between two bodies is pushed as
    // { t, a, b, speed (approach speed, px/s), x, y }.
    this.recordContacts = false;
    this.contactLog = [];
    this.pairPrev = {};
    this.pairNow = {};
  }

  var BAUMGARTE = 0.2;
  var CIRCLE_SEGMENTS = 32;

  // ---------- teleportation ----------
  // A portal is a rectangle. When a body's centre ENTERS it, the body is moved to the exit,
  // keeping its offset from the portal centre and its velocity.
  // The body is locked (cannot teleport again) until it has left every portal rectangle,
  // so exits that overlap a portal never cause endless loops. A body that starts inside a
  // portal is not teleported until it has left and re-entered.
  // o = { x, y, w, h, angle? (portal centre/size/rotation in radians),
  //       exitX, exitY, exitAngle?, velocityFactor? (default 1), rotate? (turn offset, velocity and body by the angle difference) }
  World.prototype.addPortal = function (o) {
    var p = {
      x: o.x, y: o.y, hw: o.w / 2, hh: o.h / 2, angle: o.angle || 0,
      exitX: o.exitX, exitY: o.exitY, exitAngle: o.exitAngle || 0,
      vf: o.velocityFactor !== undefined ? o.velocityFactor : 1,
      rotate: !!o.rotate
    };
    this.portals.push(p);
    return p;
  };

  function inPortal(p, x, y) {
    var dx = x - p.x, dy = y - p.y;
    var c = Math.cos(p.angle), s = Math.sin(p.angle);
    var lx = c * dx + s * dy, ly = -s * dx + c * dy;
    return Math.abs(lx) <= p.hw && Math.abs(ly) <= p.hh;
  }

  function portalAt(world, x, y) {
    for (var i = 0; i < world.portals.length; i++) if (inPortal(world.portals[i], x, y)) return world.portals[i];
    return null;
  }

  function applyPortals(world) {
    for (var i = 0; i < world.bodies.length; i++) {
      var b = world.bodies[i];
      if (b.invMass === 0) continue;
      var p = portalAt(world, b.x, b.y);
      if (b.inPortal === undefined) { b.inPortal = p !== null; continue; }   // first look: just remember
      if (!p) { b.inPortal = false; continue; }
      if (b.inPortal) continue;                                              // still locked
      var ox = b.x - p.x, oy = b.y - p.y, vx = b.vx, vy = b.vy, t;
      if (p.rotate) {
        var da = p.exitAngle - p.angle, c = Math.cos(da), s = Math.sin(da);
        t = c * ox - s * oy; oy = s * ox + c * oy; ox = t;
        t = c * vx - s * vy; vy = s * vx + c * vy; vx = t;
        b.angle += da;
      }
      b.x = p.exitX + ox; b.y = p.exitY + oy;
      b.vx = vx * p.vf; b.vy = vy * p.vf;
      b.inPortal = portalAt(world, b.x, b.y) !== null;                       // lock if the exit sits inside a portal
    }
  }

  // Wrap-around edges: leaving one side of the rectangle brings the body back on the opposite side.
  // o = { x0, y0, x1, y1, left, right, top, bottom }  (each side true/false)
  World.prototype.setWrap = function (o) {
    this.wrapBounds = {
      x0: o.x0, y0: o.y0, x1: o.x1, y1: o.y1,
      left: !!o.left, right: !!o.right, top: !!o.top, bottom: !!o.bottom
    };
  };

  function applyWrap(world) {
    var w = world.wrapBounds, bw = w.x1 - w.x0, bh = w.y1 - w.y0;
    for (var i = 0; i < world.bodies.length; i++) {
      var b = world.bodies[i];
      if (b.invMass === 0) continue;
      if (w.right && b.x > w.x1) b.x -= bw;
      else if (w.left && b.x < w.x0) b.x += bw;
      if (w.bottom && b.y > w.y1) b.y -= bh;
      else if (w.top && b.y < w.y0) b.y += bh;
    }
  }

  // ---------- explosions (grenades) ----------
  // A blast sends `rays` rays out from (x, y). The nearest body on each ray (static bodies count,
  // so walls shield what is behind them) gets an impulse along the ray, applied at the hit point,
  // which also spins bodies that are hit off-centre.
  // Strength: intensity * (1 - d/radius)^2  px/s of speed change, independent of mass.
  // o = { x, y, time (seconds from sim start), radius?, intensity?, rays? }
  World.prototype.addExplosion = function (o) {
    var e = {
      x: o.x, y: o.y, time: o.time || 0,
      radius: o.radius !== undefined ? o.radius : 400,
      intensity: o.intensity !== undefined ? o.intensity : 1200,
      rays: o.rays || 128,
      fired: false
    };
    this.explosions.push(e);
    return e;
  };

  // distance along the ray to the body, or -1 (also -1 if the ray starts inside it)
  function rayHit(b, ox, oy, dx, dy, maxT) {
    var t;
    if (b.shape === "circle") {
      var cx = ox - b.x, cy = oy - b.y;
      var bb = cx * dx + cy * dy;
      var cc = cx * cx + cy * cy - b.r * b.r;
      if (cc < 0) return -1;
      var disc = bb * bb - cc;
      if (disc < 0) return -1;
      t = -bb - Math.sqrt(disc);
      return (t >= 0 && t <= maxT) ? t : -1;
    }
    // box: rotate the ray into the box's frame and test the slabs
    var c = Math.cos(-b.angle), s = Math.sin(-b.angle);
    var px = ox - b.x, py = oy - b.y;
    var lx = c * px - s * py, ly = s * px + c * py;
    var ldx = c * dx - s * dy, ldy = s * dx + c * dy;
    var tmin = -1e30, tmax = 1e30, t1, t2, tmp;
    if (Math.abs(ldx) < 1e-12) { if (lx < -b.hw || lx > b.hw) return -1; }
    else {
      t1 = (-b.hw - lx) / ldx; t2 = (b.hw - lx) / ldx;
      if (t1 > t2) { tmp = t1; t1 = t2; t2 = tmp; }
      if (t1 > tmin) tmin = t1;
      if (t2 < tmax) tmax = t2;
    }
    if (Math.abs(ldy) < 1e-12) { if (ly < -b.hh || ly > b.hh) return -1; }
    else {
      t1 = (-b.hh - ly) / ldy; t2 = (b.hh - ly) / ldy;
      if (t1 > t2) { tmp = t1; t1 = t2; t2 = tmp; }
      if (t1 > tmin) tmin = t1;
      if (t2 < tmax) tmax = t2;
    }
    if (tmax < tmin || tmax < 0 || tmin < 0) return -1;
    return tmin <= maxT ? tmin : -1;
  }

  function fireExplosion(world, e) {
    var N = e.rays, R = e.radius, i, k;
    for (i = 0; i < N; i++) {
      var ang = 2 * Math.PI * (i + 0.5) / N;
      var dx = Math.cos(ang), dy = Math.sin(ang);
      var bestT = R, best = null;
      for (k = 0; k < world.bodies.length; k++) {
        var t = rayHit(world.bodies[k], e.x, e.y, dx, dy, bestT);
        if (t >= 0 && t < bestT) { bestT = t; best = world.bodies[k]; }
      }
      if (!best || best.invMass === 0) continue;
      var fall = 1 - bestT / R;
      fall *= fall;
      var arc = 2 * Math.PI * bestT / N;                 // gap between neighbouring rays at this distance
      var width = 2 * radiusOf(best);
      var dv = e.intensity * fall * Math.min(1, arc / width);
      var mass = 1 / best.invMass;
      var px = dx * dv * mass, py = dy * dv * mass;      // impulse
      var hx = e.x + dx * bestT, hy = e.y + dy * bestT;  // hit point
      var rx = hx - best.x, ry = hy - best.y;
      best.vx += px * best.invMass;
      best.vy += py * best.invMass;
      best.w += best.invI * (rx * py - ry * px);
    }
  }

  // ---------- water ----------
  // A water zone is an axis-aligned rectangle. It does not collide; bodies inside it feel
  //   buoyancy  : lifts a body by (waterDensity / bodyDensity) * submergedFraction * gravity,
  //               applied at the centre of the submerged area (so floating boxes self-right)
  //   drag      : velocity decays at  drag * 10 * submergedFraction  per second
  //   lift      : tilted flat bodies glide along their face as they sink (simplified plate lift,
  //               extra speed along the plate = lift * submergedFraction * 1/s * speed across it)
  // o = { x, y, w, h (x,y = centre), density?, drag?, lift? }
  World.prototype.addWater = function (o) {
    var z = {
      x0: o.x - o.w / 2, x1: o.x + o.w / 2, y0: o.y - o.h / 2, y1: o.y + o.h / 2,
      density: o.density !== undefined ? o.density : 3,
      drag: o.drag !== undefined ? o.drag : 0.3,
      lift: o.lift !== undefined ? o.lift : 0.3
    };
    this.waters.push(z);
    return z;
  };

  function clipHalf(pts, axis, limit, keepGreater) {
    var out = [], n = pts.length, i, a, b, da, db, t;
    for (i = 0; i < n; i++) {
      a = pts[i]; b = pts[(i + 1) % n];
      da = a[axis] - limit; db = b[axis] - limit;
      if (!keepGreater) { da = -da; db = -db; }
      if (da >= 0) out.push(a);
      if ((da >= 0) !== (db >= 0)) {
        t = da / (da - db);
        out.push([a[0] + t * (b[0] - a[0]), a[1] + t * (b[1] - a[1])]);
      }
    }
    return out;
  }

  // returns { frac, cx, cy } of the part of body b inside zone z, or null if none
  function submerged(b, z) {
    var poly, i;
    if (b.shape === "circle") {
      poly = [];
      for (i = 0; i < b.lp.length; i++) poly.push([b.x + b.lp[i][0], b.y + b.lp[i][1]]);
    } else {
      poly = b.wv;
    }
    var p = clipHalf(poly, 0, z.x0, true);
    if (p.length < 3) return null;
    p = clipHalf(p, 0, z.x1, false);
    if (p.length < 3) return null;
    p = clipHalf(p, 1, z.y0, true);
    if (p.length < 3) return null;
    p = clipHalf(p, 1, z.y1, false);
    if (p.length < 3) return null;
    var A = 0, cx = 0, cy = 0, n = p.length, j, cr;
    for (i = 0; i < n; i++) {
      j = (i + 1) % n;
      cr = p[i][0] * p[j][1] - p[j][0] * p[i][1];
      A += cr;
      cx += (p[i][0] + p[j][0]) * cr;
      cy += (p[i][1] + p[j][1]) * cr;
    }
    A *= 0.5;
    if (Math.abs(A) < 1e-9) return null;
    cx /= 6 * A; cy /= 6 * A;
    var frac = Math.abs(A) / b.polyArea;
    if (frac > 1) frac = 1;
    return { frac: frac, cx: cx, cy: cy };
  }

  function applyWater(world, h) {
    var gx = world.gravityX, gy = world.gravityY;
    var glen = Math.sqrt(gx * gx + gy * gy);
    for (var bi = 0; bi < world.bodies.length; bi++) {
      var b = world.bodies[bi];
      if (b.invMass === 0) continue;
      var rad = radiusOf(b);
      for (var zi = 0; zi < world.waters.length; zi++) {
        var z = world.waters[zi];
        if (b.x + rad < z.x0 || b.x - rad > z.x1 || b.y + rad < z.y0 || b.y - rad > z.y1) continue;
        var s = submerged(b, z);
        if (!s) continue;

        // buoyancy
        var a = (z.density / b.density) * s.frac;
        var ax = -gx * a, ay = -gy * a;
        b.vx += ax * h; b.vy += ay * h;
        var rx = s.cx - b.x, ry = s.cy - b.y;
        b.w += b.invI * (1 / b.invMass) * (rx * ay - ry * ax) * h;

        // drag (implicit, so it never overshoots)
        var c = z.drag * 10 * s.frac;
        var f = 1 / (1 + c * h);
        b.vx *= f; b.vy *= f; b.w *= f;

        // lift: a tilted flat body converts motion across its face into glide along it
        if (z.lift > 0 && b.shape === "box" && glen > 0) {
          var dx, dy;
          if (b.hw >= b.hh) { dx = Math.cos(b.angle); dy = Math.sin(b.angle); }
          else { dx = -Math.sin(b.angle); dy = Math.cos(b.angle); }
          var vn = b.vx * (-dy) + b.vy * dx;                       // velocity across the long axis
          var gd = (gx * dx + gy * dy) / glen;                      // how much the long axis points downhill
          var sg = gd > 0 ? 1 : (gd < 0 ? -1 : 0);
          var k = Math.min(z.lift * s.frac * h, 0.5) * Math.min(1, Math.abs(gd) * 2);
          var dvp = k * Math.abs(vn) * sg;
          b.vx += dx * dvp; b.vy += dy * dvp;
        }
      }
    }
  }

  // ---------- joints ----------

  function toLocal(body, x, y) {
    var dx = x - body.x, dy = y - body.y;
    var c = Math.cos(body.angle), s = Math.sin(body.angle);
    return [c * dx + s * dy, -s * dx + c * dy];
  }

  // Pivot (revolute) joint: both bodies share one world point.
  // o = { a, b, x, y, lower?, upper? }  limits are the allowed range of (angleB - angleA)
  // relative to the starting pose, in radians.
  World.prototype.addPivot = function (o) {
    var j = {
      type: "pivot", a: o.a, b: o.b,
      la: toLocal(o.a, o.x, o.y), lb: toLocal(o.b, o.x, o.y),
      ref: o.b.angle - o.a.angle,
      lower: o.lower, upper: o.upper,
      collide: !!o.collide
    };
    j.hasLimit = (o.lower !== undefined && o.lower !== null) || (o.upper !== undefined && o.upper !== null);
    this.joints.push(j);
    return j;
  };

  // Distance joint: keeps two world points a fixed distance apart.
  // o = { a, b, ax, ay, bx, by, frequency?, damping? }
  // frequency (Hz) = 0 or missing -> rigid; > 0 -> springy; damping is a ratio (0 = none, 1 = critical).
  World.prototype.addDistance = function (o) {
    var dx = o.bx - o.ax, dy = o.by - o.ay;
    var j = {
      type: "distance", a: o.a, b: o.b,
      la: toLocal(o.a, o.ax, o.ay), lb: toLocal(o.b, o.bx, o.by),
      length: Math.sqrt(dx * dx + dy * dy),
      frequency: o.frequency || 0,
      damping: o.damping !== undefined ? o.damping : 0.3,
      collide: !!o.collide,
      hasLimit: false
    };
    this.joints.push(j);
    return j;
  };

  // Spring joint: a bouncy distance joint. Rest length = distance between the two points
  // when the joint is created. Defaults: 1.5 Hz, damping 0.1 (springy at pixel-scale gravity).
  World.prototype.addSpring = function (o) {
    var j = this.addDistance({
      a: o.a, b: o.b, ax: o.ax, ay: o.ay, bx: o.bx, by: o.by,
      frequency: o.frequency !== undefined && o.frequency > 0 ? o.frequency : 1.5,
      damping: o.damping !== undefined ? o.damping : 0.1,
      collide: o.collide
    });
    j.isSpring = true;
    return j;
  };

  function prepareDistance(j, h) {
    var a = j.a, b = j.b;
    var ca = Math.cos(a.angle), sa = Math.sin(a.angle);
    var cb = Math.cos(b.angle), sb = Math.sin(b.angle);
    j.rax = ca * j.la[0] - sa * j.la[1];
    j.ray = sa * j.la[0] + ca * j.la[1];
    j.rbx = cb * j.lb[0] - sb * j.lb[1];
    j.rby = sb * j.lb[0] + cb * j.lb[1];
    var dx = (b.x + j.rbx) - (a.x + j.rax), dy = (b.y + j.rby) - (a.y + j.ray);
    var len = Math.sqrt(dx * dx + dy * dy);
    if (len > 1e-6) { j.ux = dx / len; j.uy = dy / len; } else { j.ux = 1; j.uy = 0; }
    var crA = j.rax * j.uy - j.ray * j.ux;
    var crB = j.rbx * j.uy - j.rby * j.ux;
    var invMass = a.invMass + b.invMass + a.invI * crA * crA + b.invI * crB * crB;
    var C = len - j.length;
    j.gamma = 0;
    if (j.frequency > 0 && invMass > 0) {
      var m = 1 / invMass;
      var omega = 2 * Math.PI * j.frequency;
      var d = 2 * m * j.damping * omega;
      var k = m * omega * omega;
      var g = h * (d + h * k);
      j.gamma = g !== 0 ? 1 / g : 0;
      j.bias = C * h * k * j.gamma;
      invMass += j.gamma;
    } else {
      j.bias = BAUMGARTE / h * C;
    }
    j.effMass = invMass !== 0 ? 1 / invMass : 0;
    j.accImp = 0;
  }

  function solveDistance(j) {
    var a = j.a, b = j.b;
    var vax = a.vx - a.w * j.ray, vay = a.vy + a.w * j.rax;
    var vbx = b.vx - b.w * j.rby, vby = b.vy + b.w * j.rbx;
    var cdot = j.ux * (vbx - vax) + j.uy * (vby - vay);
    var imp = -j.effMass * (cdot + j.bias + j.gamma * j.accImp);
    j.accImp += imp;
    var px = imp * j.ux, py = imp * j.uy;
    a.vx -= a.invMass * px; a.vy -= a.invMass * py;
    a.w -= a.invI * (j.rax * py - j.ray * px);
    b.vx += b.invMass * px; b.vy += b.invMass * py;
    b.w += b.invI * (j.rbx * py - j.rby * px);
  }

  // Weld joint: glues two bodies together at a world point (position AND angle locked).
  // frequency (Hz) = 0 or missing -> fully rigid; > 0 -> the bond can flex like a stiff spring.
  // o = { a, b, x, y, frequency?, damping? }
  World.prototype.addWeld = function (o) {
    var j = {
      type: "weld", a: o.a, b: o.b,
      la: toLocal(o.a, o.x, o.y), lb: toLocal(o.b, o.x, o.y),
      ref: o.b.angle - o.a.angle,
      frequency: o.frequency || 0,
      damping: o.damping !== undefined ? o.damping : 0.5,
      collide: !!o.collide,
      hasLimit: false
    };
    this.joints.push(j);
    return j;
  };

  function prepareWeldAngle(j, h) {
    var a = j.a, b = j.b;
    var invI = a.invI + b.invI;
    var C = b.angle - a.angle - j.ref;
    j.wGamma = 0;
    j.wImp = 0;
    if (invI === 0) { j.wMass = 0; j.wBias = 0; return; }
    if (j.frequency > 0) {
      var m = 1 / invI;
      var omega = 2 * Math.PI * j.frequency;
      var d = 2 * m * j.damping * omega;
      var k = m * omega * omega;
      var g = h * (d + h * k);
      j.wGamma = g !== 0 ? 1 / g : 0;
      j.wBias = C * h * k * j.wGamma;
      invI += j.wGamma;
    } else {
      j.wBias = BAUMGARTE / h * C;
    }
    j.wMass = 1 / invI;
  }

  function solveWeldAngle(j) {
    var a = j.a, b = j.b;
    if (j.wMass === 0) return;
    var imp = -j.wMass * ((b.w - a.w) + j.wBias + j.wGamma * j.wImp);
    j.wImp += imp;
    a.w -= a.invI * imp;
    b.w += b.invI * imp;
  }


  // Piston joint: b may only slide along an axis fixed in a's frame, and cannot rotate relative to a.
  // o = { a, b, x, y, axisAngle (radians, world, at creation), lower?, upper? (px along the axis, 0 = start),
  //       speed? (motor, px/s along the axis, a -> b direction), accel? (motor limit, px/s^2 of the effective mass) }
  World.prototype.addPiston = function (o) {
    var ca = Math.cos(-o.a.angle), sa = Math.sin(-o.a.angle);
    var ux = Math.cos(o.axisAngle), uy = Math.sin(o.axisAngle);
    var j = {
      type: "piston", a: o.a, b: o.b,
      la: toLocal(o.a, o.x, o.y), lb: toLocal(o.b, o.x, o.y),
      axL: [ca * ux - sa * uy, sa * ux + ca * uy],
      ref: o.b.angle - o.a.angle,
      frequency: 0,
      lower: o.lower, upper: o.upper,
      speed: o.speed || 0,
      accel: o.accel !== undefined && o.accel > 0 ? o.accel : 1e6,
      hasMotor: o.speed !== undefined && o.speed !== null && o.speed !== 0,
      collide: !!o.collide,
      hasLimit: false
    };
    this.joints.push(j);
    return j;
  };

  function cross2(ax, ay, bx, by) { return ax * by - ay * bx; }

  function preparePiston(j, h) {
    var a = j.a, b = j.b;
    prepareWeldAngle(j, h);
    var ca = Math.cos(a.angle), sa = Math.sin(a.angle);
    var cb = Math.cos(b.angle), sb = Math.sin(b.angle);
    j.rax = ca * j.la[0] - sa * j.la[1];
    j.ray = sa * j.la[0] + ca * j.la[1];
    j.rbx = cb * j.lb[0] - sb * j.lb[1];
    j.rby = sb * j.lb[0] + cb * j.lb[1];
    var dx = (b.x + j.rbx) - (a.x + j.rax), dy = (b.y + j.rby) - (a.y + j.ray);
    j.ux = ca * j.axL[0] - sa * j.axL[1];
    j.uy = sa * j.axL[0] + ca * j.axL[1];
    j.nx = -j.uy; j.ny = j.ux;
    j.h = h;
    // perpendicular row
    j.pa1 = cross2(dx + j.rax - 0, dy + j.ray - 0, j.nx, j.ny);
    j.pa1 = cross2(dx + j.rax, dy + j.ray, j.nx, j.ny);
    j.pa2 = cross2(j.rbx, j.rby, j.nx, j.ny);
    var kp = a.invMass + b.invMass + a.invI * j.pa1 * j.pa1 + b.invI * j.pa2 * j.pa2;
    j.pMass = kp > 0 ? 1 / kp : 0;
    j.pBias = BAUMGARTE / h * (dx * j.nx + dy * j.ny);
    // axial row
    j.aa1 = cross2(dx + j.rax, dy + j.ray, j.ux, j.uy);
    j.aa2 = cross2(j.rbx, j.rby, j.ux, j.uy);
    var ka = a.invMass + b.invMass + a.invI * j.aa1 * j.aa1 + b.invI * j.aa2 * j.aa2;
    j.aMass = ka > 0 ? 1 / ka : 0;
    j.trans = dx * j.ux + dy * j.uy;
    j.lowerImp = 0; j.upperImp = 0; j.motorImp = 0;
  }

  function applyAxis(j, ex, ey, ea1, ea2, imp) {
    var a = j.a, b = j.b;
    a.vx -= a.invMass * imp * ex; a.vy -= a.invMass * imp * ey; a.w -= a.invI * imp * ea1;
    b.vx += b.invMass * imp * ex; b.vy += b.invMass * imp * ey; b.w += b.invI * imp * ea2;
  }

  function axialCdot(j) {
    var a = j.a, b = j.b;
    return j.ux * (b.vx - a.vx) + j.uy * (b.vy - a.vy) + j.aa2 * b.w - j.aa1 * a.w;
  }

  function solvePiston(j) {
    var a = j.a, b = j.b, imp, C, newImp;
    solveWeldAngle(j);
    // motor
    if (j.hasMotor && j.aMass > 0) {
      imp = -j.aMass * (axialCdot(j) - j.speed);
      var maxImp = j.accel * j.aMass * j.h;
      newImp = Math.max(-maxImp, Math.min(maxImp, j.motorImp + imp));
      imp = newImp - j.motorImp; j.motorImp = newImp;
      applyAxis(j, j.ux, j.uy, j.aa1, j.aa2, imp);
    }
    // limits
    if (j.aMass > 0) {
      if (j.lower !== undefined && j.lower !== null) {
        C = j.trans - j.lower;
        imp = -j.aMass * (axialCdot(j) + (C > 0 ? C / j.h : BAUMGARTE * C / j.h));
        newImp = Math.max(j.lowerImp + imp, 0);
        imp = newImp - j.lowerImp; j.lowerImp = newImp;
        applyAxis(j, j.ux, j.uy, j.aa1, j.aa2, imp);
      }
      if (j.upper !== undefined && j.upper !== null) {
        C = j.upper - j.trans;
        imp = -j.aMass * (-axialCdot(j) + (C > 0 ? C / j.h : BAUMGARTE * C / j.h));
        newImp = Math.max(j.upperImp + imp, 0);
        imp = newImp - j.upperImp; j.upperImp = newImp;
        applyAxis(j, j.ux, j.uy, j.aa1, j.aa2, -imp);
      }
    }
    // perpendicular lock
    if (j.pMass > 0) {
      var cdot = j.nx * (b.vx - a.vx) + j.ny * (b.vy - a.vy) + j.pa2 * b.w - j.pa1 * a.w;
      imp = -j.pMass * (cdot + j.pBias);
      applyAxis(j, j.nx, j.ny, j.pa1, j.pa2, imp);
    }
  }

  function prepareJoint(j, h) {
    if (j.type === "piston") { preparePiston(j, h); return; }
    if (j.type === "distance") prepareDistance(j, h);
    else {
      preparePivot(j, h);
      if (j.type === "weld") prepareWeldAngle(j, h);
    }
  }

  function solveJoint(j) {
    if (j.type === "piston") { solvePiston(j); return; }
    if (j.type === "distance") solveDistance(j);
    else {
      if (j.type === "weld") solveWeldAngle(j);
      solvePivot(j);
    }
  }

  function preparePivot(j, h) {
    var a = j.a, b = j.b;
    var ca = Math.cos(a.angle), sa = Math.sin(a.angle);
    var cb = Math.cos(b.angle), sb = Math.sin(b.angle);
    j.rax = ca * j.la[0] - sa * j.la[1];
    j.ray = sa * j.la[0] + ca * j.la[1];
    j.rbx = cb * j.lb[0] - sb * j.lb[1];
    j.rby = sb * j.lb[0] + cb * j.lb[1];
    var ma = a.invMass, mb = b.invMass, ia = a.invI, ib = b.invI;
    j.k11 = ma + mb + ia * j.ray * j.ray + ib * j.rby * j.rby;
    j.k12 = -ia * j.rax * j.ray - ib * j.rbx * j.rby;
    j.k22 = ma + mb + ia * j.rax * j.rax + ib * j.rbx * j.rbx;
    var det = j.k11 * j.k22 - j.k12 * j.k12;
    j.invDet = det !== 0 ? 1 / det : 0;
    j.biasX = BAUMGARTE / h * ((b.x + j.rbx) - (a.x + j.rax));
    j.biasY = BAUMGARTE / h * ((b.y + j.rby) - (a.y + j.ray));
    j.angMass = (ia + ib) > 0 ? 1 / (ia + ib) : 0;
    j.relAngle = b.angle - a.angle - j.ref;
    j.lowerImp = 0;
    j.upperImp = 0;
    j.h = h;
  }

  function solvePivot(j) {
    var a = j.a, b = j.b;
    var ma = a.invMass, mb = b.invMass, ia = a.invI, ib = b.invI;
    var imp;

    if (j.hasLimit && j.angMass > 0) {
      var cdot, C, newImp;
      if (j.lower !== undefined && j.lower !== null) {
        C = j.relAngle - j.lower;
        cdot = b.w - a.w;
        imp = -j.angMass * (cdot + (C > 0 ? C / j.h : BAUMGARTE * C / j.h));
        newImp = Math.max(j.lowerImp + imp, 0);
        imp = newImp - j.lowerImp;
        j.lowerImp = newImp;
        a.w -= ia * imp;
        b.w += ib * imp;
      }
      if (j.upper !== undefined && j.upper !== null) {
        C = j.upper - j.relAngle;
        cdot = a.w - b.w;
        imp = -j.angMass * (cdot + (C > 0 ? C / j.h : BAUMGARTE * C / j.h));
        newImp = Math.max(j.upperImp + imp, 0);
        imp = newImp - j.upperImp;
        j.upperImp = newImp;
        a.w += ia * imp;
        b.w -= ib * imp;
      }
    }

    // point-to-point constraint
    var cdx = (b.vx - b.w * j.rby) - (a.vx - a.w * j.ray) + j.biasX;
    var cdy = (b.vy + b.w * j.rbx) - (a.vy + a.w * j.rax) + j.biasY;
    var px = -j.invDet * (j.k22 * cdx - j.k12 * cdy);
    var py = -j.invDet * (-j.k12 * cdx + j.k11 * cdy);
    a.vx -= ma * px; a.vy -= ma * py;
    a.w -= ia * (j.rax * py - j.ray * px);
    b.vx += mb * px; b.vy += mb * py;
    b.w += ib * (j.rbx * py - j.rby * px);
  }

  function jointBlocksContact(world, A, B) {
    for (var i = 0; i < world.joints.length; i++) {
      var j = world.joints[i];
      if (j.collide) continue;
      if ((j.a === A && j.b === B) || (j.a === B && j.b === A)) return true;
    }
    return false;
  }

  // ---------- body creation ----------

  function finishBody(b, density) {
    b.density = density;
    if (b.isStatic) {
      b.invMass = 0;
      b.invI = 0;
    } else {
      var area = b.shape === "circle" ? Math.PI * b.r * b.r : 4 * b.hw * b.hh;
      var m = Math.max(area * density, 0.0001);
      var I = b.shape === "circle"
        ? 0.5 * m * b.r * b.r
        : m * (4 * b.hw * b.hw + 4 * b.hh * b.hh) / 12;
      b.invMass = 1 / m;
      b.invI = 1 / I;
    }
    return b;
  }

  function baseBody(o) {
    return {
      x: o.x, y: o.y, angle: o.angle || 0,
      // NOTE: o.w is the box WIDTH, so initial spin comes from o.av (rad/s)
      vx: o.vx || 0, vy: o.vy || 0, w: o.av || 0,
      restitution: o.restitution !== undefined ? o.restitution : 0.3,
      friction: o.friction !== undefined ? o.friction : 0.5,
      isStatic: !!o.isStatic, label: o.label,
      gravityScale: o.gravityScale !== undefined ? o.gravityScale : 1,
      // Triggers (static bodies): world.time of every new touch is pushed onto hits.
      // sensor = true -> things pass through it (touch is still recorded)
      isTrigger: !!o.trigger, sensor: !!o.sensor,
      hits: [], touching: false, touchNow: false,
      invMass: 0, invI: 0
    };
  }

  World.prototype.register = function (b) {
    this.bodies.push(b);
    if (b.isTrigger) this.triggers.push(b);
    return b;
  };

  World.prototype.addCircle = function (o) {
    var b = baseBody(o);
    b.shape = "circle";
    b.r = o.r;
    // polygon approximation, used only for water (submerged area) calculations
    b.lp = [];
    for (var s = 0; s < CIRCLE_SEGMENTS; s++) {
      var t = 2 * Math.PI * s / CIRCLE_SEGMENTS;
      b.lp.push([Math.cos(t) * b.r, Math.sin(t) * b.r]);
    }
    b.polyArea = 0.5 * CIRCLE_SEGMENTS * b.r * b.r * Math.sin(2 * Math.PI / CIRCLE_SEGMENTS);
    finishBody(b, o.density !== undefined ? o.density : 1);
    return this.register(b);
  };

  World.prototype.addBox = function (o) {
    var b = baseBody(o);
    b.shape = "box";
    b.hw = o.w / 2;
    b.hh = o.h / 2;
    b.lv = [[-b.hw, -b.hh], [b.hw, -b.hh], [b.hw, b.hh], [-b.hw, b.hh]];
    b.ln = [];
    for (var i = 0; i < 4; i++) {
      var a = b.lv[i], c = b.lv[(i + 1) % 4];
      var ex = c[0] - a[0], ey = c[1] - a[1];
      var len = Math.sqrt(ex * ex + ey * ey);
      var nx = ey / len, ny = -ex / len;
      // make sure the normal points away from the centre (local origin)
      if (nx * ((a[0] + c[0]) / 2) + ny * ((a[1] + c[1]) / 2) < 0) { nx = -nx; ny = -ny; }
      b.ln.push([nx, ny]);
    }
    b.wv = [[0, 0], [0, 0], [0, 0], [0, 0]];
    b.wn = [[0, 0], [0, 0], [0, 0], [0, 0]];
    b.polyArea = 4 * b.hw * b.hh;
    finishBody(b, o.density !== undefined ? o.density : 1);
    return this.register(b);
  };

  function updateWorldShape(b) {
    if (b.shape !== "box") return;
    var c = Math.cos(b.angle), s = Math.sin(b.angle);
    for (var i = 0; i < 4; i++) {
      var lv = b.lv[i], ln = b.ln[i];
      b.wv[i][0] = b.x + c * lv[0] - s * lv[1];
      b.wv[i][1] = b.y + s * lv[0] + c * lv[1];
      b.wn[i][0] = c * ln[0] - s * ln[1];
      b.wn[i][1] = s * ln[0] + c * ln[1];
    }
  }

  // ---------- collision detection ----------
  // Every function returns null or {nx, ny, pts:[{x,y,pen}]}
  // with the normal pointing from body A towards body B.

  function circleCircle(A, B) {
    var dx = B.x - A.x, dy = B.y - A.y;
    var rs = A.r + B.r;
    var d2 = dx * dx + dy * dy;
    if (d2 >= rs * rs) return null;
    var d = Math.sqrt(d2);
    var nx = 1, ny = 0;
    if (d > 1e-9) { nx = dx / d; ny = dy / d; }
    var pen = rs - d;
    return {
      nx: nx, ny: ny,
      pts: [{ x: A.x + nx * (A.r - pen / 2), y: A.y + ny * (A.r - pen / 2), pen: pen }]
    };
  }

  // normal points from the polygon towards the circle
  function circlePoly(C, P) {
    var best = -1e30, idx = 0, i;
    for (i = 0; i < 4; i++) {
      var s = P.wn[i][0] * (C.x - P.wv[i][0]) + P.wn[i][1] * (C.y - P.wv[i][1]);
      if (s > C.r) return null;
      if (s > best) { best = s; idx = i; }
    }
    var v1 = P.wv[idx], v2 = P.wv[(idx + 1) % 4];
    var ex = v2[0] - v1[0], ey = v2[1] - v1[1];
    var d1 = (C.x - v1[0]) * ex + (C.y - v1[1]) * ey;
    var d2 = (C.x - v2[0]) * (-ex) + (C.y - v2[1]) * (-ey);
    var nx, ny, pen, px, py, dist, ax, ay;
    if (d1 <= 0 || d2 <= 0) {
      var vx = d1 <= 0 ? v1[0] : v2[0];
      var vy = d1 <= 0 ? v1[1] : v2[1];
      ax = C.x - vx; ay = C.y - vy;
      dist = Math.sqrt(ax * ax + ay * ay);
      if (dist > C.r) return null;
      if (dist < 1e-9) { nx = P.wn[idx][0]; ny = P.wn[idx][1]; }
      else { nx = ax / dist; ny = ay / dist; }
      pen = C.r - dist;
      px = vx; py = vy;
    } else {
      nx = P.wn[idx][0]; ny = P.wn[idx][1];
      pen = C.r - best;
      px = C.x - nx * best; py = C.y - ny * best;
    }
    return { nx: nx, ny: ny, pts: [{ x: px, y: py, pen: pen }] };
  }

  function bestFace(A, B) {
    // largest separation of B along A's face normals (negative = overlap)
    var best = -1e30, idx = 0;
    for (var i = 0; i < 4; i++) {
      var nx = A.wn[i][0], ny = A.wn[i][1];
      var vx = A.wv[i][0], vy = A.wv[i][1];
      var minD = 1e30;
      for (var j = 0; j < 4; j++) {
        var d = nx * (B.wv[j][0] - vx) + ny * (B.wv[j][1] - vy);
        if (d < minD) minD = d;
      }
      if (minD > best) { best = minD; idx = i; }
    }
    return { sep: best, idx: idx };
  }

  function polyPoly(A, B) {
    var fa = bestFace(A, B);
    if (fa.sep > 0) return null;
    var fb = bestFace(B, A);
    if (fb.sep > 0) return null;

    var ref, inc, flip, fi;
    if (fa.sep >= fb.sep - 0.001) { ref = A; inc = B; flip = false; fi = fa.idx; }
    else { ref = B; inc = A; flip = true; fi = fb.idx; }

    var rn = ref.wn[fi];
    var r1 = ref.wv[fi], r2 = ref.wv[(fi + 1) % 4];

    // incident edge: the edge of the other polygon most anti-parallel to rn
    var ii = 0, minDot = 1e30, i;
    for (i = 0; i < 4; i++) {
      var dd = rn[0] * inc.wn[i][0] + rn[1] * inc.wn[i][1];
      if (dd < minDot) { minDot = dd; ii = i; }
    }
    var p1 = [inc.wv[ii][0], inc.wv[ii][1]];
    var p2 = [inc.wv[(ii + 1) % 4][0], inc.wv[(ii + 1) % 4][1]];

    // clip against the side planes of the reference face
    var tx = r2[0] - r1[0], ty = r2[1] - r1[1];
    var tl = Math.sqrt(tx * tx + ty * ty);
    tx /= tl; ty /= tl;
    var pts = clipSegment(p1, p2, tx, ty, r1[0] * tx + r1[1] * ty, true);
    if (pts.length < 2) return null;
    pts = clipSegment(pts[0], pts[1], tx, ty, r2[0] * tx + r2[1] * ty, false);
    if (pts.length < 2) return null;

    var out = [];
    for (i = 0; i < 2; i++) {
      var sep = rn[0] * (pts[i][0] - r1[0]) + rn[1] * (pts[i][1] - r1[1]);
      if (sep <= 0) out.push({ x: pts[i][0], y: pts[i][1], pen: -sep });
    }
    if (out.length === 0) return null;
    var nx = flip ? -rn[0] : rn[0];
    var ny = flip ? -rn[1] : rn[1];
    return { nx: nx, ny: ny, pts: out };
  }

  // keep the part of the segment where dot(t,p) >= offset (keepAbove) or <= offset
  function clipSegment(p1, p2, tx, ty, offset, keepAbove) {
    var d1 = p1[0] * tx + p1[1] * ty - offset;
    var d2 = p2[0] * tx + p2[1] * ty - offset;
    if (!keepAbove) { d1 = -d1; d2 = -d2; }
    var out = [];
    if (d1 >= 0) out.push(p1);
    if (d2 >= 0) out.push(p2);
    if (d1 * d2 < 0) {
      var t = d1 / (d1 - d2);
      out.push([p1[0] + t * (p2[0] - p1[0]), p1[1] + t * (p2[1] - p1[1])]);
    }
    return out;
  }

  function collide(A, B) {
    if (A.shape === "circle" && B.shape === "circle") return circleCircle(A, B);
    if (A.shape === "box" && B.shape === "box") return polyPoly(A, B);
    if (A.shape === "circle") {
      var m = circlePoly(A, B);          // normal: polygon -> circle (B -> A)
      if (!m) return null;
      m.nx = -m.nx; m.ny = -m.ny;        // we need A -> B
      return m;
    }
    return circlePoly(B, A);              // A is polygon, B is circle: already A -> B
  }

  // ---------- stepping ----------

  World.prototype.step = function (dt) {
    var n = this.substeps, h = dt / n, s, i;
    for (i = 0; i < this.explosions.length; i++) {
      var e = this.explosions[i];
      if (!e.fired && this.time >= e.time - 1e-9) { e.fired = true; fireExplosion(this, e); }
    }
    for (s = 0; s < n; s++) {
      this.subTime = this.time + s * h;
      this.substep(h);
    }
    this.time += dt;
  };

  World.prototype.substep = function (h) {
    var bodies = this.bodies, i, j, k, b;

    for (i = 0; i < bodies.length; i++) updateWorldShape(bodies[i]);

    this.pairNow = {};
    for (k = 0; k < this.triggers.length; k++) this.triggers[k].touchNow = false;

    // gather contacts
    var contacts = [];
    for (i = 0; i < bodies.length; i++) {
      for (j = i + 1; j < bodies.length; j++) {
        var A = bodies[i], B = bodies[j];
        if (A.invMass === 0 && B.invMass === 0) continue;
        if (!roughOverlap(A, B)) continue;
        if (this.joints.length && jointBlocksContact(this, A, B)) continue;
        var m = collide(A, B);
        if (!m) continue;
        if (A.isTrigger || B.isTrigger) {
          var trig = A.isTrigger ? A : B;
          if (!trig.touching && !trig.touchNow) trig.hits.push(this.subTime);
          trig.touchNow = true;
          if (trig.sensor) continue;                    // sensors record the touch but never push back
        }
        if (this.recordContacts) {
          var pk = i + "," + j;
          this.pairNow[pk] = true;
          if (!this.pairPrev[pk]) {
            var best = 0, bp = m.pts[0], q;
            for (k = 0; k < m.pts.length; k++) {
              q = m.pts[k];
              var sv = -(((B.vx - B.w * (q.y - B.y)) - (A.vx - A.w * (q.y - A.y))) * m.nx +
                         ((B.vy + B.w * (q.x - B.x)) - (A.vy + A.w * (q.x - A.x))) * m.ny);
              if (sv < 0) sv = 0;
              if (sv >= best) { best = sv; bp = q; }
            }
            this.contactLog.push({ t: this.subTime, a: A, b: B, speed: best, x: bp.x, y: bp.y });
          }
        }
        var e = Math.max(A.restitution, B.restitution);
        var mu = Math.sqrt(A.friction * B.friction);
        for (k = 0; k < m.pts.length; k++) {
          var p = m.pts[k];
          var rax = p.x - A.x, ray = p.y - A.y, rbx = p.x - B.x, rby = p.y - B.y;
          var rvx = (B.vx - B.w * rby) - (A.vx - A.w * ray);
          var rvy = (B.vy + B.w * rbx) - (A.vy + A.w * rax);
          var vn = rvx * m.nx + rvy * m.ny;
          var rnA = rax * m.ny - ray * m.nx;
          var rnB = rbx * m.ny - rby * m.nx;
          var tx = -m.ny, ty = m.nx;
          var rtA = rax * ty - ray * tx;
          var rtB = rbx * ty - rby * tx;
          contacts.push({
            a: A, b: B, nx: m.nx, ny: m.ny, tx: tx, ty: ty,
            rax: rax, ray: ray, rbx: rbx, rby: rby,
            massN: 1 / (A.invMass + B.invMass + rnA * rnA * A.invI + rnB * rnB * B.invI),
            massT: 1 / (A.invMass + B.invMass + rtA * rtA * A.invI + rtB * rtB * B.invI),
            bias: (vn < -60) ? -e * (vn + 0) : 0,   // bounce only above a speed threshold (px/s)
            mu: mu, pen: p.pen, jn: 0, jt: 0
          });
        }
      }
    }

    for (k = 0; k < this.triggers.length; k++) this.triggers[k].touching = this.triggers[k].touchNow;
    this.pairPrev = this.pairNow;

    // apply gravity
    for (i = 0; i < bodies.length; i++) {
      b = bodies[i];
      if (b.invMass === 0) continue;
      b.vx += this.gravityX * h * b.gravityScale;
      b.vy += this.gravityY * h * b.gravityScale;
    }

    // bias must be measured after gravity so resting contacts do not bounce
    for (k = 0; k < contacts.length; k++) {
      var c = contacts[k];
      var rvx2 = (c.b.vx - c.b.w * c.rby) - (c.a.vx - c.a.w * c.ray);
      var rvy2 = (c.b.vy + c.b.w * c.rbx) - (c.a.vy + c.a.w * c.rax);
      var vn2 = rvx2 * c.nx + rvy2 * c.ny;
      c.bias = (vn2 < -60) ? -Math.max(c.a.restitution, c.b.restitution) * vn2 : 0;
    }

    // water forces (buoyancy, drag, lift)
    if (this.waters.length) applyWater(this, h);

    // joints are prepared once per substep, after gravity
    for (k = 0; k < this.joints.length; k++) prepareJoint(this.joints[k], h);

    // sequential impulses
    for (var it = 0; it < this.iterations; it++) {
      for (k = 0; k < this.joints.length; k++) solveJoint(this.joints[k]);
      for (k = 0; k < contacts.length; k++) {
        var c2 = contacts[k], a = c2.a, bb = c2.b;

        // normal
        var dvx = (bb.vx - bb.w * c2.rby) - (a.vx - a.w * c2.ray);
        var dvy = (bb.vy + bb.w * c2.rbx) - (a.vy + a.w * c2.rax);
        var vn3 = dvx * c2.nx + dvy * c2.ny;
        var dj = c2.massN * (-vn3 + c2.bias);
        var newJn = Math.max(c2.jn + dj, 0);
        dj = newJn - c2.jn;
        c2.jn = newJn;
        applyImpulse(a, bb, c2, dj * c2.nx, dj * c2.ny);

        // friction
        dvx = (bb.vx - bb.w * c2.rby) - (a.vx - a.w * c2.ray);
        dvy = (bb.vy + bb.w * c2.rbx) - (a.vy + a.w * c2.rax);
        var vt = dvx * c2.tx + dvy * c2.ty;
        var djt = -c2.massT * vt;
        var maxF = c2.mu * c2.jn;
        var newJt = Math.max(-maxF, Math.min(maxF, c2.jt + djt));
        djt = newJt - c2.jt;
        c2.jt = newJt;
        applyImpulse(a, bb, c2, djt * c2.tx, djt * c2.ty);
      }
    }

    // integrate positions
    for (i = 0; i < bodies.length; i++) {
      b = bodies[i];
      if (b.invMass === 0) continue;
      b.x += b.vx * h;
      b.y += b.vy * h;
      b.angle += b.w * h;
    }

    // positional correction (push overlapping bodies apart)
    for (k = 0; k < contacts.length; k++) {
      var c3 = contacts[k];
      var corr = Math.max(c3.pen - 0.05, 0) * 0.4;
      if (corr <= 0) continue;
      var tot = c3.a.invMass + c3.b.invMass;
      var sa = c3.a.invMass / tot, sb = c3.b.invMass / tot;
      c3.a.x -= c3.nx * corr * sa; c3.a.y -= c3.ny * corr * sa;
      c3.b.x += c3.nx * corr * sb; c3.b.y += c3.ny * corr * sb;
    }

    if (this.portals.length) applyPortals(this);
    if (this.wrapBounds) applyWrap(this);
  };

  function applyImpulse(a, b, c, px, py) {
    a.vx -= px * a.invMass; a.vy -= py * a.invMass;
    a.w -= a.invI * (c.rax * py - c.ray * px);
    b.vx += px * b.invMass; b.vy += py * b.invMass;
    b.w += b.invI * (c.rbx * py - c.rby * px);
  }

  function radiusOf(b) {
    return b.shape === "circle" ? b.r : Math.sqrt(b.hw * b.hw + b.hh * b.hh);
  }

  function roughOverlap(A, B) {
    var dx = A.x - B.x, dy = A.y - B.y;
    var r = radiusOf(A) + radiusOf(B);
    return dx * dx + dy * dy <= r * r;
  }

  return { World: World };
})();



// ---------------------------------------------------------------
// Tumble panel for After Effects  (ExtendScript, ES3)
// Select layers -> Simulate -> position + rotation keyframes are baked.
// Layers whose name starts with "static" are immovable obstacles.
// Per-layer overrides live in the layer comment, on a line like:
//   tumble: density=2; friction=0.8; bounce=0.5; gravity=0.5; shape=circle
// ---------------------------------------------------------------
(function (thisObj) {

  var STATIC_PREFIX = "static_";
  var TAG = "tumble:";
  var KEYS = ["shape", "density", "friction", "bounce", "gravity", "drag", "lift", "radius", "intensity", "rays", "velocity", "rotate", "sensor", "loop", "base"];
  var MARK_RE = /^(static|water|grenade|portal|exit|trigger)[_ \-]*/i;

  function trim(s) { return String(s).replace(/^\s+|\s+$/g, ""); }

  function isStaticLayer(layer) {
    return layer.name.toLowerCase().indexOf("static") === 0;
  }

  // layers named water_* are liquid zones (their rectangle is the water)
  function isWaterLayer(layer) {
    return layer.name.toLowerCase().indexOf("water") === 0;
  }

  // layers named grenade_* are explosions: position = blast centre, in-point = detonation time
  function isGrenadeLayer(layer) {
    return layer.name.toLowerCase().indexOf("grenade") === 0;
  }

  // layers named trigger_* start their own keyframe animation the moment something touches them
  function isTriggerLayer(layer) { return layer.name.toLowerCase().indexOf("trigger") === 0; }

  // portal_<id> sends bodies to the layer exit_<id>
  function isPortalLayer(layer) { return layer.name.toLowerCase().indexOf("portal") === 0; }
  function isExitLayer(layer) { return layer.name.toLowerCase().indexOf("exit") === 0; }
  function portalId(layer) { return layer.name.replace(MARK_RE, "").toLowerCase(); }

  // ---------- per-layer settings (stored in the layer comment) ----------

  function splitLines(text) { return String(text || "").split(/\r\n|\r|\n/); }

  function parseSettings(layer) {
    var out = {};
    var lines = splitLines(layer.comment);
    for (var i = 0; i < lines.length; i++) {
      var ln = trim(lines[i]);
      if (ln.toLowerCase().indexOf(TAG) !== 0) continue;
      var parts = ln.substr(TAG.length).split(";");
      for (var p = 0; p < parts.length; p++) {
        var kv = parts[p].split("=");
        if (kv.length < 2) continue;
        var key = trim(kv[0]).toLowerCase();
        var val = trim(kv[1]);
        if (key === "shape") {
          val = val.toLowerCase();
          if (val === "circle" || val === "box") out.shape = val;
        } else {
          var num = parseFloat(val);
          if (!isNaN(num)) out[key] = num;
        }
      }
    }
    return out;
  }

  function writeSettings(layer, s) {
    var keep = [];
    var lines = splitLines(layer.comment);
    for (var i = 0; i < lines.length; i++) {
      if (trim(lines[i]).toLowerCase().indexOf(TAG) !== 0 && trim(lines[i]) !== "") keep.push(lines[i]);
    }
    var bits = [];
    for (var k = 0; k < KEYS.length; k++) {
      var key = KEYS[k];
      if (s[key] !== undefined && s[key] !== "") bits.push(key + "=" + s[key]);
    }
    if (bits.length) keep.push(TAG + " " + bits.join("; "));
    layer.comment = keep.join("\r");
  }

  function hasKeys(s) {
    for (var k = 0; k < KEYS.length; k++) if (s[KEYS[k]] !== undefined) return true;
    return false;
  }

  function pick(layerValue, globalValue) {
    return layerValue !== undefined ? layerValue : globalValue;
  }

  // ---------- joints (stored in the comment of the "child" layer) ----------
  // joint: pivot; with=<other layer name>; lower=-30; upper=45      (limits in degrees, optional)
  // The pivot point is the position of the "with" layer (its anchor point in the comp).

  var JOINT_TAG = "joint:";

  function parseJoints(layer) {
    var out = [];
    var lines = splitLines(layer.comment);
    for (var i = 0; i < lines.length; i++) {
      var ln = trim(lines[i]);
      if (ln.toLowerCase().indexOf(JOINT_TAG) !== 0) continue;
      var parts = ln.substr(JOINT_TAG.length).split(";");
      var j = { type: trim(parts[0]).toLowerCase() };
      for (var p = 1; p < parts.length; p++) {
        var eq = parts[p].indexOf("=");
        if (eq < 0) continue;
        var key = trim(parts[p].substr(0, eq)).toLowerCase();
        var val = trim(parts[p].substr(eq + 1));
        if (key === "with") j.withName = val;
        else if (key === "lower" || key === "upper" || key === "hz" || key === "damping" || key === "speed" || key === "accel") {
          var n = parseFloat(val);
          if (!isNaN(n)) j[key] = n;
        }
      }
      if ((j.type === "pivot" || j.type === "distance" || j.type === "spring" || j.type === "weld" || j.type === "piston") && j.withName) out.push(j);
    }
    return out;
  }

  function jointLineText(j) {
    var s = JOINT_TAG + " " + j.type + "; with=" + j.withName;
    if (j.lower !== undefined) s += "; lower=" + j.lower;
    if (j.upper !== undefined) s += "; upper=" + j.upper;
    if (j.hz !== undefined) s += "; hz=" + j.hz;
    if (j.damping !== undefined) s += "; damping=" + j.damping;
    if (j.speed !== undefined) s += "; speed=" + j.speed;
    if (j.accel !== undefined) s += "; accel=" + j.accel;
    return s;
  }

  // keep every line except joint lines that satisfy dropFn(jointLineParsed)
  function rewriteJointLines(layer, dropFn) {
    var lines = splitLines(layer.comment), keep = [], i;
    for (i = 0; i < lines.length; i++) {
      var ln = trim(lines[i]);
      if (ln === "") continue;
      if (ln.toLowerCase().indexOf(JOINT_TAG) === 0) {
        var tmp = { comment: ln };
        var parsed = parseJoints(tmp);
        if (parsed.length && dropFn(parsed[0])) continue;
      }
      keep.push(lines[i]);
    }
    return keep;
  }

  function findLayerByName(comp, name) {
    for (var i = 1; i <= comp.numLayers; i++) if (comp.layer(i).name === name) return comp.layer(i);
    return null;
  }

  function countName(comp, name) {
    var n = 0;
    for (var i = 1; i <= comp.numLayers; i++) if (comp.layer(i).name === name) n++;
    return n;
  }

  // params: { lower, upper } for pivot, { hz, damping } for distance (each optional)
  function addJoint(type, params) {
    var comp = app.project.activeItem;
    if (!(comp instanceof CompItem)) { alert("Open a composition first."); return; }
    var sel = comp.selectedLayers;
    if (sel.length !== 2) { alert("Select exactly 2 layers.\nJoints connect the layers' position (anchor) points."); return; }
    var a = sel[0], b = sel[1];                       // a = top-most selected layer
    if (a.index > b.index) { var t = a; a = b; b = t; }
    if (countName(comp, a.name) > 1) { alert("Layer name \"" + a.name + "\" is used more than once. Give the layers unique names first."); return; }
    var j = { type: type, withName: a.name };
    var k;
    for (k in params) if (params[k] !== undefined) j[k] = params[k];
    app.beginUndoGroup("Add " + type + " joint");
    var keep = rewriteJointLines(b, function (e) { return e.withName === a.name && e.type === type; });
    keep.push(jointLineText(j));
    b.comment = keep.join("\r");
    app.endUndoGroup();
    if (type === "pivot") alert("Pivot joint added: \"" + b.name + "\" pivots around the position of \"" + a.name + "\".");
    else if (type === "piston") alert("Piston joint added: \"" + b.name + "\" slides along its own rotation axis through the position of \"" + a.name + "\".");
    else if (type === "weld") alert("Weld joint added: \"" + b.name + "\" is glued to \"" + a.name + "\" at the position of \"" + a.name + "\".");
    else alert(type.charAt(0).toUpperCase() + type.substr(1) + " joint added between the positions of \"" + a.name + "\" and \"" + b.name + "\".");
  }

  function removeJoints() {
    var comp = app.project.activeItem;
    if (!(comp instanceof CompItem) || comp.selectedLayers.length === 0) { alert("Select layers first."); return; }
    var names = {}, i, n = 0;
    for (i = 0; i < comp.selectedLayers.length; i++) names[comp.selectedLayers[i].name] = true;
    app.beginUndoGroup("Remove joints");
    for (i = 1; i <= comp.numLayers; i++) {
      var l = comp.layer(i);
      var own = names[l.name] === true;
      var before = parseJoints(l).length;
      if (before === 0) continue;
      var keep = rewriteJointLines(l, function (e) { return own || names[e.withName] === true; });
      l.comment = keep.join("\r");
      n += before - parseJoints(l).length;
    }
    app.endUndoGroup();
    alert("Removed " + n + " joint(s).");
  }

  // ---------- geometry ----------

  function guessShape(layer, fallback) {
    var n = layer.name.toLowerCase();
    if (n.indexOf("circle") !== -1 || n.indexOf("ball") !== -1) return "circle";
    if (n.indexOf("box") !== -1 || n.indexOf("rect") !== -1) return "box";
    return fallback;
  }

  function rad(d) { return d * Math.PI / 180; }
  function deg(r) { return r * 180 / Math.PI; }

  // Everything we need to know about a layer at time t
  function readLayer(layer, t) {
    var tr = layer.transform;
    var pos = tr.position.valueAtTime(t, false);
    var anchor = tr.anchorPoint.valueAtTime(t, false);
    var scale = tr.scale.valueAtTime(t, false);
    var rot = tr.rotation.valueAtTime(t, false);
    var rect = layer.sourceRectAtTime(t, false);
    var sx = Math.abs(scale[0]) / 100, sy = Math.abs(scale[1]) / 100;
    var w = rect.width * sx, h = rect.height * sy;
    // centre of the layer's content, as an offset from the position, in layer-local space
    var ox = (rect.left + rect.width / 2 - anchor[0]) * (scale[0] / 100);
    var oy = (rect.top + rect.height / 2 - anchor[1]) * (scale[1] / 100);
    var a = rad(rot);
    var c = Math.cos(a), s = Math.sin(a);
    return {
      cx: pos[0] + c * ox - s * oy,
      cy: pos[1] + s * ox + c * oy,
      ox: ox, oy: oy, w: w, h: h, angle: a
    };
  }

  function setKeys(prop, times, values) {
    while (prop.numKeys > 0) prop.removeKey(prop.numKeys);
    try {
      prop.setValuesAtTimes(times, values);
    } catch (e) {
      for (var i = 0; i < times.length; i++) prop.setValueAtTime(times[i], values[i]);
    }
  }

  // ---------- Triggermatic: re-time a layer's own keyframes ----------

  // every keyframed property anywhere under a layer (skips markers and value-less properties)
  function collectKeyedProps(group, out) {
    var n = group.numProperties, i, p;
    for (i = 1; i <= n; i++) {
      p = group.property(i);
      if (p.propertyType === PropertyType.PROPERTY) {
        if (p.numKeys > 0 && p.matchName !== "ADBE Marker" &&
            p.propertyValueType !== PropertyValueType.NO_VALUE && p.propertyValueType !== PropertyValueType.CUSTOM_VALUE) out.push(p);
      } else {
        collectKeyedProps(p, out);
      }
    }
    return out;
  }

  function readKeys(prop) {
    var keys = [], i, k;
    for (i = 1; i <= prop.numKeys; i++) {
      k = { t: prop.keyTime(i), v: prop.keyValue(i), inT: prop.keyInInterpolationType(i), outT: prop.keyOutInterpolationType(i) };
      try { k.inE = prop.keyInTemporalEase(i); k.outE = prop.keyOutTemporalEase(i); } catch (e1) {}
      try { k.tCont = prop.keyTemporalContinuous(i); k.tAuto = prop.keyTemporalAutoBezier(i); } catch (e2) {}
      if (prop.isSpatial) {
        try {
          k.inS = prop.keyInSpatialTangent(i); k.outS = prop.keyOutSpatialTangent(i);
          k.sCont = prop.keySpatialContinuous(i); k.sAuto = prop.keySpatialAutoBezier(i);
        } catch (e3) {}
      }
      keys.push(k);
    }
    return keys;
  }

  function writeKeys(prop, keys) {
    while (prop.numKeys > 0) prop.removeKey(prop.numKeys);
    var i, k, idx;
    for (i = 0; i < keys.length; i++) prop.setValueAtTime(keys[i].t, keys[i].v);
    for (i = 0; i < keys.length; i++) {
      k = keys[i];
      idx = prop.nearestKeyIndex(k.t);
      try { prop.setInterpolationTypeAtKey(idx, k.inT, k.holdOut ? KeyframeInterpolationType.HOLD : k.outT); } catch (e1) {}
      if (!k.holdOut && k.inE && k.outE) { try { prop.setTemporalEaseAtKey(idx, k.inE, k.outE); } catch (e2) {} }
      if (!k.holdOut && k.tCont !== undefined) {
        try { prop.setTemporalContinuousAtKey(idx, k.tCont); prop.setTemporalAutoBezierAtKey(idx, k.tAuto); } catch (e3) {}
      }
      if (k.inS && k.outS) {
        try {
          prop.setSpatialTangentsAtKey(idx, k.inS, k.outS);
          prop.setSpatialContinuousAtKey(idx, k.sCont); prop.setSpatialAutoBezierAtKey(idx, k.sAuto);
        } catch (e4) {}
      }
    }
  }

  function firstKeyTime(props) {
    var first = 1e30;
    for (var i = 0; i < props.length; i++) if (props[i].keyTime(1) < first) first = props[i].keyTime(1);
    return first;
  }

  // Lay out copies of the keys so the animation starts at each time in `starts`.
  // With several starts, a run that is still playing when the next one begins is cut off
  // (its last key is set to HOLD so the value jumps back to the start when the next run begins).
  function layoutRuns(keys, firstT, starts) {
    var out = [], s, j, t, kept, cut, c;
    for (s = 0; s < starts.length; s++) {
      var next = s + 1 < starts.length ? starts[s + 1] : 1e30;
      kept = 0; cut = false;
      for (j = 0; j < keys.length; j++) {
        t = starts[s] + (keys[j].t - firstT);
        if (t < next - 1e-6) {
          c = {};
          for (var p in keys[j]) c[p] = keys[j][p];
          c.t = t; c.holdOut = false;
          out.push(c); kept++;
        } else cut = true;
      }
      if (cut && kept > 0) out[out.length - 1].holdOut = true;
    }
    return out;
  }

  // hits = absolute comp times; returns how many properties were re-timed
  function retimeTrigger(layer, hits, restart) {
    var props = collectKeyedProps(layer, []);
    if (props.length === 0) return -1;
    var ls = parseSettings(layer);
    var current = firstKeyTime(props);
    var base = ls.base !== undefined ? ls.base : current;
    if (ls.base === undefined) { ls.base = Math.round(current * 1000000) / 1000000; writeSettings(layer, ls); }
    var starts = hits.length ? (restart ? hits : [hits[0]]) : [base];
    for (var i = 0; i < props.length; i++) {
      var keys = readKeys(props[i]);
      writeKeys(props[i], layoutRuns(keys, current, starts));
    }
    return props.length;
  }

  // ---------- contact markers ----------
  var HIT_TAG = "Hit: ";

  function writeContactMarkers(comp, log, start, minSpeed, dt) {
    var mp = comp.markerProperty, i, e, n = 0, last = {}, key, nm1, nm2, t;
    // remove markers from a previous run
    for (i = mp.numKeys; i >= 1; i--) {
      var mv = mp.keyValue(i);
      if (mv && mv.comment && mv.comment.indexOf(HIT_TAG) === 0) mp.removeKey(i);
    }
    for (i = 0; i < log.length; i++) {
      e = log[i];
      if (e.speed < minSpeed) continue;
      nm1 = e.a.label || "Edge"; nm2 = e.b.label || "Edge";
      key = nm1 + "|" + nm2;
      t = start + e.t;
      if (last[key] !== undefined && t - last[key] < 2 * dt) continue;   // same pair, same instant
      last[key] = t;
      mp.setValueAtTime(t, new MarkerValue(HIT_TAG + nm1 + " + " + nm2 + " (" + Math.round(e.speed) + " px/s)"));
      n++;
    }
    return n;
  }

  // ---------- simulate ----------

  function makeBody(world, layer, info, opts, isStatic, extra) {
    var ls = parseSettings(layer);
    var shape = ls.shape || guessShape(layer, isStatic ? "box" : opts.shape);
    var common = {
      label: layer.name,
      x: info.cx, y: info.cy, angle: info.angle, isStatic: isStatic,
      density: pick(ls.density, opts.density),
      friction: pick(ls.friction, opts.friction),
      restitution: pick(ls.bounce, opts.bounce),
      gravityScale: pick(ls.gravity, 1)
    };
    if (extra) { for (var xk in extra) common[xk] = extra[xk]; }
    if (shape === "circle") {
      common.r = (info.w + info.h) / 4;
      return world.addCircle(common);
    }
    common.w = info.w;
    common.h = info.h;
    return world.addBox(common);
  }

  function simulate(opts) {
    var comp = app.project.activeItem;
    if (!(comp instanceof CompItem)) { alert("Open a composition first."); return; }

    var sel = comp.selectedLayers;
    if (sel.length === 0) { alert("Select the layers you want to simulate."); return; }

    var start = comp.time;
    var fps = 1 / comp.frameDuration;
    var endTime = opts.seconds > 0 ? Math.min(start + opts.seconds, comp.duration) : comp.duration;
    var frames = Math.floor((endTime - start) * fps + 0.0001) + 1;
    if (frames < 2) { alert("Move the current time earlier, or increase the duration."); return; }

    var world = new Tumble.World({ gravity: opts.gravity });
    world.recordContacts = opts.contactSpeed > 0;
    var items = [];
    var skipped = [];
    var bodyOf = {};          // layer.index -> body
    var dynamicIdx = {};      // layer.index -> true for layers being simulated
    var jointNotes = [];
    var triggerReport = [];
    var contactCount = 0;
    var i, layer, info, body;

    // dynamic bodies = selected layers (unless named static)
    for (i = 0; i < sel.length; i++) {
      layer = sel[i];
      if (isStaticLayer(layer) || isWaterLayer(layer) || isGrenadeLayer(layer) || isPortalLayer(layer) || isExitLayer(layer) || isTriggerLayer(layer)) continue;
      if (layer.threeDLayer || layer.parent || layer.nullLayer || !layer.sourceRectAtTime) {
        skipped.push(layer.name);
        continue;
      }
      info = readLayer(layer, start);
      body = makeBody(world, layer, info, opts, false);
      bodyOf[layer.index] = body;
      dynamicIdx[layer.index] = true;
      items.push({
        layer: layer, body: body, ox: info.ox, oy: info.oy,
        times: [], pos: [], rot: []
      });
    }
    if (items.length === 0) { alert("No usable layers selected (3D, parented, null and static-named layers are skipped)."); return; }

    // static obstacles = any layer named static*
    for (i = 1; i <= comp.numLayers; i++) {
      layer = comp.layer(i);
      if (!isStaticLayer(layer) || !layer.sourceRectAtTime || layer.threeDLayer || layer.parent) continue;
      if (bodyOf[layer.index]) continue;
      bodyOf[layer.index] = makeBody(world, layer, readLayer(layer, start), opts, true);
    }

    // triggers: trigger_* layers are fixed bodies that remember when they get touched
    var triggerItems = [], tl, tset;
    for (i = 1; i <= comp.numLayers; i++) {
      tl = comp.layer(i);
      if (!isTriggerLayer(tl) || !tl.sourceRectAtTime || tl.threeDLayer || tl.parent) continue;
      tset = parseSettings(tl);
      bodyOf[tl.index] = makeBody(world, tl, readLayer(tl, start), opts, true,
        { trigger: true, sensor: pick(tset.sensor, 0) >= 0.5 });
      triggerItems.push({ layer: tl, body: bodyOf[tl.index], restart: pick(tset.loop, 0) >= 0.5 });
    }

    // joints: any layer whose comment holds a "joint:" line, if at least one end is simulated.
    // A partner that is neither selected nor static-named is pinned in place as a fixed anchor.
    var jl, jj, js, partner, bodyA, bodyB, pv;
    for (i = 1; i <= comp.numLayers; i++) {
      jl = comp.layer(i);
      js = parseJoints(jl);
      for (jj = 0; jj < js.length; jj++) {
        partner = findLayerByName(comp, js[jj].withName);
        if (!partner) { jointNotes.push("\"" + jl.name + "\": partner \"" + js[jj].withName + "\" not found"); continue; }
        if (!dynamicIdx[jl.index] && !dynamicIdx[partner.index]) continue;
        var ends = [jl, partner], e;
        for (e = 0; e < 2; e++) {
          if (!bodyOf[ends[e].index]) {
            if (ends[e].threeDLayer || !ends[e].sourceRectAtTime) { bodyOf[ends[e].index] = null; continue; }
            bodyOf[ends[e].index] = makeBody(world, ends[e], readLayer(ends[e], start), opts, true);
          }
        }
        bodyA = bodyOf[partner.index];
        bodyB = bodyOf[jl.index];
        if (!bodyA || !bodyB) { jointNotes.push("\"" + jl.name + "\": a joint end is 3D or has no content"); continue; }
        pv = partner.transform.position.valueAtTime(start, false);
        if (js[jj].type === "distance" || js[jj].type === "spring") {
          var pb = jl.transform.position.valueAtTime(start, false);
          var dOpts = {
            a: bodyA, b: bodyB, ax: pv[0], ay: pv[1], bx: pb[0], by: pb[1],
            frequency: js[jj].hz, damping: js[jj].damping
          };
          if (js[jj].type === "spring") world.addSpring(dOpts); else world.addDistance(dOpts);
        } else if (js[jj].type === "piston") {
          world.addPiston({
            a: bodyA, b: bodyB, x: pv[0], y: pv[1],
            axisAngle: rad(jl.transform.rotation.valueAtTime(start, false)),
            lower: js[jj].lower, upper: js[jj].upper,
            speed: js[jj].speed, accel: js[jj].accel
          });
        } else if (js[jj].type === "weld") {
          world.addWeld({ a: bodyA, b: bodyB, x: pv[0], y: pv[1], frequency: js[jj].hz, damping: js[jj].damping });
        } else {
          world.addPivot({
            a: bodyA, b: bodyB, x: pv[0], y: pv[1],
            lower: js[jj].lower !== undefined ? rad(js[jj].lower) : undefined,
            upper: js[jj].upper !== undefined ? rad(js[jj].upper) : undefined
          });
        }
      }
    }

    // water zones: any layer named water_*
    var waterCount = 0, wl, wset, winfo;
    for (i = 1; i <= comp.numLayers; i++) {
      wl = comp.layer(i);
      if (!isWaterLayer(wl) || !wl.sourceRectAtTime || wl.threeDLayer || wl.parent) continue;
      winfo = readLayer(wl, start);
      wset = parseSettings(wl);
      world.addWater({
        x: winfo.cx, y: winfo.cy, w: winfo.w, h: winfo.h,
        density: pick(wset.density, 3), drag: pick(wset.drag, 0.3), lift: pick(wset.lift, 0.3)
      });
      waterCount++;
      if (Math.abs(winfo.angle) > 0.001) jointNotes.push("water \"" + wl.name + "\" is rotated; its rotation is ignored (treated as a straight rectangle)");
    }

    // grenades: any layer named grenade_*; detonates at the layer's in-point
    var grenadeCount = 0, gl, gset, gt, gpos;
    for (i = 1; i <= comp.numLayers; i++) {
      gl = comp.layer(i);
      if (!isGrenadeLayer(gl) || gl.threeDLayer) continue;
      gt = gl.inPoint;
      if (gt < start - 1e-6) { jointNotes.push("grenade \"" + gl.name + "\" goes off before the simulation starts (in-point " + (Math.round(gt * 100) / 100) + "s), skipped"); continue; }
      if (gt > endTime + 1e-6) continue;
      gset = parseSettings(gl);
      gpos = gl.transform.position.valueAtTime(gt, false);
      world.addExplosion({
        x: gpos[0], y: gpos[1], time: Math.max(0, gt - start),
        radius: pick(gset.radius, 400), intensity: pick(gset.intensity, 1200), rays: pick(gset.rays, 128)
      });
      grenadeCount++;
    }

    // portals: portal_<id> layers send bodies to the matching exit_<id> layer
    var portalCount = 0, pl2, ex2, pset, pinfo, einfo, pid, q;
    for (i = 1; i <= comp.numLayers; i++) {
      pl2 = comp.layer(i);
      if (!isPortalLayer(pl2) || !pl2.sourceRectAtTime || pl2.threeDLayer) continue;
      pid = portalId(pl2);
      ex2 = null;
      for (q = 1; q <= comp.numLayers; q++) {
        if (isExitLayer(comp.layer(q)) && portalId(comp.layer(q)) === pid) { ex2 = comp.layer(q); break; }
      }
      if (!ex2 || !ex2.sourceRectAtTime) { jointNotes.push("portal \"" + pl2.name + "\" has no exit layer named exit_" + pid); continue; }
      pinfo = readLayer(pl2, start);
      einfo = readLayer(ex2, start);
      pset = parseSettings(pl2);
      world.addPortal({
        x: pinfo.cx, y: pinfo.cy, w: pinfo.w, h: pinfo.h, angle: pinfo.angle,
        exitX: einfo.cx, exitY: einfo.cy, exitAngle: einfo.angle,
        velocityFactor: pick(pset.velocity, 1), rotate: pick(pset.rotate, 0) >= 0.5
      });
      portalCount++;
    }

    // comp edges: each can be None, a solid Wall, or Wrap (leave one side, re-enter on the other)
    var T = 400, W = comp.width, H = comp.height, BIG = 100000;
    var wallOpts = { isStatic: true, friction: opts.friction, restitution: opts.bounce };
    function addWall(x, y, w, h) { wallOpts.x = x; wallOpts.y = y; wallOpts.w = w; wallOpts.h = h; world.addBox(wallOpts); }
    if (opts.wallBottom === "wall") addWall(W / 2, H + T / 2, BIG, T);
    if (opts.wallTop === "wall") addWall(W / 2, -T / 2, BIG, T);
    if (opts.wallLeft === "wall") addWall(-T / 2, H / 2, T, BIG);
    if (opts.wallRight === "wall") addWall(W + T / 2, H / 2, T, BIG);
    if (opts.wallTop === "wrap" || opts.wallBottom === "wrap" || opts.wallLeft === "wrap" || opts.wallRight === "wrap") {
      world.setWrap({
        x0: 0, y0: 0, x1: W, y1: H,
        left: opts.wallLeft === "wrap", right: opts.wallRight === "wrap",
        top: opts.wallTop === "wrap", bottom: opts.wallBottom === "wrap"
      });
    }

    // run the simulation, recording every frame
    var dt = comp.frameDuration;
    var f, k, it, a, c, s, b;
    for (f = 0; f < frames; f++) {
      for (k = 0; k < items.length; k++) {
        it = items[k]; b = it.body;
        a = b.angle; c = Math.cos(a); s = Math.sin(a);
        it.times.push(start + f * dt);
        it.pos.push([b.x - (c * it.ox - s * it.oy), b.y - (s * it.ox + c * it.oy)]);
        it.rot.push(deg(a));
      }
      world.step(dt);
    }

    // bake keyframes
    app.beginUndoGroup("Tumble simulation");
    try {
      for (k = 0; k < items.length; k++) {
        it = items[k];
        var tr = it.layer.transform;
        if (tr.position.dimensionsSeparated) {
          var xs = [], ys = [];
          for (f = 0; f < it.pos.length; f++) { xs.push(it.pos[f][0]); ys.push(it.pos[f][1]); }
          setKeys(tr.xPosition, it.times, xs);
          setKeys(tr.yPosition, it.times, ys);
        } else {
          setKeys(tr.position, it.times, it.pos);
        }
        setKeys(tr.rotation, it.times, it.rot);
      }

      // triggers: start each trigger layer's own animation at the moment of contact
      for (k = 0; k < triggerItems.length; k++) {
        var ti = triggerItems[k], absHits = [], hq;
        for (hq = 0; hq < ti.body.hits.length; hq++) absHits.push(start + ti.body.hits[hq]);
        var moved = retimeTrigger(ti.layer, absHits, ti.restart);
        if (moved < 0) jointNotes.push("trigger \"" + ti.layer.name + "\" has no keyframes to start");
        else triggerReport.push(ti.layer.name + ": " + absHits.length + " touch(es)");
      }

      // contacts: one comp marker per impact faster than the chosen speed
      if (world.recordContacts) contactCount = writeContactMarkers(comp, world.contactLog, start, opts.contactSpeed, dt);
    } finally {
      app.endUndoGroup();
    }

    var msg = "Simulated " + items.length + " layer(s) over " + frames + " frames.";
    if (waterCount) msg += "\nWater zones: " + waterCount;
    if (grenadeCount) msg += "\nGrenades: " + grenadeCount;
    if (portalCount) msg += "\nPortals: " + portalCount;
    if (world.recordContacts) msg += "\nContact markers: " + contactCount;
    if (triggerReport.length) msg += "\nTriggers: " + triggerReport.join("; ");
    if (world.joints.length) msg += "\nJoints used: " + world.joints.length;
    if (jointNotes.length) msg += "\nNotes: " + jointNotes.join("; ");
    if (skipped.length) msg += "\nSkipped (3D / parented / null): " + skipped.join(", ");
    alert(msg);
  }

  // ---------- layer helpers used by the buttons ----------

  function selectedOrAlert() {
    var comp = app.project.activeItem;
    if (!(comp instanceof CompItem) || comp.selectedLayers.length === 0) { alert("Select layers first."); return null; }
    return comp.selectedLayers;
  }

  // prefix = "static_" or "water_"; on=false removes either prefix
  function toggleMark(on, prefix) {
    var sel = selectedOrAlert();
    if (!sel) return;
    app.beginUndoGroup(on ? "Mark " + prefix : "Unmark layers");
    for (var i = 0; i < sel.length; i++) {
      var l = sel[i];
      var hasAny = MARK_RE.test(l.name);
      if (on) {
        if (hasAny) l.name = l.name.replace(MARK_RE, "");
        l.name = prefix + l.name;
      } else if (hasAny) {
        l.name = l.name.replace(MARK_RE, "");
      }
    }
    app.endUndoGroup();
  }

  function applyToSelected(values) {
    var sel = selectedOrAlert();
    if (!sel) return;
    app.beginUndoGroup("Tumble layer settings");
    for (var i = 0; i < sel.length; i++) {
      var s = parseSettings(sel[i]);
      for (var k = 0; k < KEYS.length; k++) {
        if (values[KEYS[k]] !== undefined) s[KEYS[k]] = values[KEYS[k]];
      }
      writeSettings(sel[i], s);
    }
    app.endUndoGroup();
  }

  function clearSelected() {
    var sel = selectedOrAlert();
    if (!sel) return;
    app.beginUndoGroup("Clear Tumble settings");
    for (var i = 0; i < sel.length; i++) writeSettings(sel[i], {});
    app.endUndoGroup();
  }

  function randomizeSelected(key, min, max) {
    var sel = selectedOrAlert();
    if (!sel) return;
    if (max < min) { var tmp = min; min = max; max = tmp; }
    app.beginUndoGroup("Tumble randomize " + key);
    for (var i = 0; i < sel.length; i++) {
      var s = parseSettings(sel[i]);
      var v = min + Math.random() * (max - min);
      s[key] = Math.round(v * 1000) / 1000;
      writeSettings(sel[i], s);
    }
    app.endUndoGroup();
  }

  function describe(layer) {
    var s = parseSettings(layer);
    if (!hasKeys(s)) return layer.name + ": no overrides";
    var bits = [];
    for (var k = 0; k < KEYS.length; k++) if (s[KEYS[k]] !== undefined) bits.push(KEYS[k] + "=" + s[KEYS[k]]);
    return layer.name + ": " + bits.join(", ");
  }

  // ---------------- UI ----------------
  function buildUI(thisObj) {
    var win = (thisObj instanceof Panel) ? thisObj : new Window("palette", "Tumble", undefined, { resizeable: true });
    win.orientation = "column";
    win.alignChildren = ["fill", "top"];
    win.margins = 12;
    win.spacing = 6;

    function row(parent, label, value) {
      var g = parent.add("group");
      g.orientation = "row";
      var t = g.add("statictext", undefined, label);
      t.preferredSize.width = 110;
      var e = g.add("edittext", undefined, String(value));
      e.preferredSize.width = 70;
      return e;
    }
    function num(e, dflt) { var v = parseFloat(e.text); return isNaN(v) ? dflt : v; }

    // ----- global settings -----
    var g1 = win.add("group");
    var t1 = g1.add("statictext", undefined, "Default shape");
    t1.preferredSize.width = 110;
    var shapeDD = g1.add("dropdownlist", undefined, ["Box", "Circle"]);
    shapeDD.selection = 0;

    var gravity = row(win, "Gravity (px/s²)", 980);
    var bounce = row(win, "Bounciness 0-1", 0.3);
    var friction = row(win, "Friction 0-1", 0.5);
    var density = row(win, "Density", 1);
    var seconds = row(win, "Seconds (0 = to end)", 0);
    var contactSpd = row(win, "Hit markers: min speed (0 = off)", 0);
    // comp edges: None / Wall / Wrap
    function edgeRow(label, dflt) {
      var g = win.add("group");
      var t = g.add("statictext", undefined, label);
      t.preferredSize.width = 110;
      var dd = g.add("dropdownlist", undefined, ["None", "Wall", "Wrap"]);
      dd.selection = dflt;
      return dd;
    }
    var edgeTop = edgeRow("Top edge", 0);
    var edgeBottom = edgeRow("Bottom edge", 1);
    var edgeLeft = edgeRow("Left edge", 1);
    var edgeRight = edgeRow("Right edge", 1);
    function edgeMode(dd, dflt) {
      var i = (dd.selection && typeof dd.selection.index === "number") ? dd.selection.index : dflt;
      return i === 1 ? "wall" : (i === 2 ? "wrap" : "none");
    }

    var go = win.add("button", undefined, "Simulate selected layers");
    var g2 = win.add("group");
    var mk = g2.add("button", undefined, "Mark static");
    var mw = g2.add("button", undefined, "Mark water");
    var mg = g2.add("button", undefined, "Mark grenade");
    var g2b = win.add("group");
    var mp = g2b.add("button", undefined, "Mark portal");
    var me = g2b.add("button", undefined, "Mark exit");
    var mt = g2b.add("button", undefined, "Mark trigger");
    var g2c = win.add("group");
    var um = g2c.add("button", undefined, "Unmark");

    // ----- per-layer overrides -----
    var pl = win.add("panel", undefined, "Selected layer overrides (blank = use default)");
    pl.orientation = "column";
    pl.alignChildren = ["fill", "top"];
    pl.margins = 10;
    var g3 = pl.add("group");
    var t3 = g3.add("statictext", undefined, "Shape");
    t3.preferredSize.width = 110;
    var lShape = g3.add("dropdownlist", undefined, ["(default)", "Box", "Circle"]);
    lShape.selection = 0;
    var lDensity = row(pl, "Density", "");
    var lFriction = row(pl, "Friction", "");
    var lBounce = row(pl, "Bounciness", "");
    var lGravity = row(pl, "Gravity scale", "");
    var lDrag = row(pl, "Water drag (water layers)", "");
    var lLift = row(pl, "Water lift (water layers)", "");
    var lRadius = row(pl, "Blast radius (grenades)", "");
    var lIntensity = row(pl, "Blast intensity (grenades)", "");
    var lVelocity = row(pl, "Portal speed factor", "");
    var lRotate = row(pl, "Portal rotates 0/1", "");
    var lSensor = row(pl, "Trigger pass-through 0/1", "");
    var lLoop = row(pl, "Trigger restarts on touch 0/1", "");
    var g4 = pl.add("group");
    var apply = g4.add("button", undefined, "Apply");
    var load = g4.add("button", undefined, "Show");
    var clear = g4.add("button", undefined, "Clear");

    // ----- joints -----
    var jp = win.add("panel", undefined, "Joints (select 2 layers)");
    jp.orientation = "column";
    jp.alignChildren = ["fill", "top"];
    jp.margins = 10;
    var jLower = row(jp, "Lower limit (° / piston px)", "");
    var jUpper = row(jp, "Upper limit (° / piston px)", "");
    var jHz = row(jp, "Elasticity (Hz)", "");
    var jDamp = row(jp, "Damping 0-1", "");
    var jSpeed = row(jp, "Piston motor speed (px/s)", "");
    var jAccel = row(jp, "Piston motor max accel", "");
    var g6 = jp.add("group");
    var addPivot = g6.add("button", undefined, "Add Pivot");
    var addDist = g6.add("button", undefined, "Add Distance");
    var g7 = jp.add("group");
    var addSpring = g7.add("button", undefined, "Add Spring");
    var addWeld = g7.add("button", undefined, "Add Weld");
    var g8 = jp.add("group");
    var addPiston = g8.add("button", undefined, "Add Piston");
    var rmJoints = g8.add("button", undefined, "Remove joints");

    // ----- randomizer -----
    var rp = win.add("panel", undefined, "Randomizer (selected layers)");
    rp.orientation = "column";
    rp.alignChildren = ["fill", "top"];
    rp.margins = 10;
    var g5 = rp.add("group");
    var t5 = g5.add("statictext", undefined, "Property");
    t5.preferredSize.width = 110;
    var rProp = g5.add("dropdownlist", undefined, ["Bounciness", "Friction", "Density", "Gravity scale"]);
    rProp.selection = 0;
    var rMin = row(rp, "Min", 0);
    var rMax = row(rp, "Max", 1);
    var rGo = rp.add("button", undefined, "Randomize");

    var hint = win.add("statictext", undefined,
      "Start time = current time.\nNames with 'circle'/'ball' become circles.\nLayers named static_* are fixed obstacles.\nLayers named water_* are liquid zones (set Density = water density, default 3; drag 0.3; lift 0.3).\nLayers named grenade_* explode at their in-point, centred on their position (radius 400, intensity 1200).\nportal_X sends bodies to the layer exit_X (set speed factor / rotate on the portal).\ntrigger_* layers play their own keyframes from the moment they are touched (re-timed on every Simulate).\nEdges: Wall = solid, Wrap = leave one side, re-enter on the opposite side.\nOverrides and joints are stored in layer comments.\nPivot point = position of the top-most selected layer.", { multiline: true });
    hint.preferredSize.height = 196;

    go.onClick = function () {
      simulate({
        shape: shapeDD.selection && shapeDD.selection.index === 1 ? "circle" : "box",
        gravity: num(gravity, 980),
        bounce: Math.max(0, Math.min(1, num(bounce, 0.3))),
        friction: Math.max(0, num(friction, 0.5)),
        density: Math.max(0.0001, num(density, 1)),
        seconds: num(seconds, 0),
        contactSpeed: Math.max(0, num(contactSpd, 0)),
        wallTop: edgeMode(edgeTop, 0), wallBottom: edgeMode(edgeBottom, 1),
        wallLeft: edgeMode(edgeLeft, 1), wallRight: edgeMode(edgeRight, 1)
      });
    };
    mk.onClick = function () { toggleMark(true, STATIC_PREFIX); };
    mw.onClick = function () { toggleMark(true, "water_"); };
    mg.onClick = function () { toggleMark(true, "grenade_"); };
    mp.onClick = function () { toggleMark(true, "portal_"); };
    me.onClick = function () { toggleMark(true, "exit_"); };
    mt.onClick = function () { toggleMark(true, "trigger_"); };
    um.onClick = function () { toggleMark(false, ""); };

    apply.onClick = function () {
      var v = {};
      var si = lShape.selection ? lShape.selection.index : 0;
      if (si === 1) v.shape = "box";
      if (si === 2) v.shape = "circle";
      if (trim(lDensity.text) !== "" && !isNaN(parseFloat(lDensity.text))) v.density = Math.max(0.0001, parseFloat(lDensity.text));
      if (trim(lFriction.text) !== "" && !isNaN(parseFloat(lFriction.text))) v.friction = Math.max(0, parseFloat(lFriction.text));
      if (trim(lBounce.text) !== "" && !isNaN(parseFloat(lBounce.text))) v.bounce = Math.max(0, Math.min(1, parseFloat(lBounce.text)));
      if (trim(lGravity.text) !== "" && !isNaN(parseFloat(lGravity.text))) v.gravity = parseFloat(lGravity.text);
      if (trim(lDrag.text) !== "" && !isNaN(parseFloat(lDrag.text))) v.drag = Math.max(0, parseFloat(lDrag.text));
      if (trim(lLift.text) !== "" && !isNaN(parseFloat(lLift.text))) v.lift = Math.max(0, parseFloat(lLift.text));
      if (trim(lRadius.text) !== "" && !isNaN(parseFloat(lRadius.text))) v.radius = Math.max(1, parseFloat(lRadius.text));
      if (trim(lIntensity.text) !== "" && !isNaN(parseFloat(lIntensity.text))) v.intensity = Math.max(0, parseFloat(lIntensity.text));
      if (trim(lVelocity.text) !== "" && !isNaN(parseFloat(lVelocity.text))) v.velocity = Math.max(0, parseFloat(lVelocity.text));
      if (trim(lRotate.text) !== "" && !isNaN(parseFloat(lRotate.text))) v.rotate = parseFloat(lRotate.text) >= 0.5 ? 1 : 0;
      if (trim(lSensor.text) !== "" && !isNaN(parseFloat(lSensor.text))) v.sensor = parseFloat(lSensor.text) >= 0.5 ? 1 : 0;
      if (trim(lLoop.text) !== "" && !isNaN(parseFloat(lLoop.text))) v.loop = parseFloat(lLoop.text) >= 0.5 ? 1 : 0;
      applyToSelected(v);
    };
    clear.onClick = function () { clearSelected(); };
    load.onClick = function () {
      var sel = selectedOrAlert();
      if (!sel) return;
      var lines = [];
      for (var i = 0; i < sel.length && i < 15; i++) lines.push(describe(sel[i]));
      if (sel.length > 15) lines.push("... and " + (sel.length - 15) + " more");
      alert(lines.join("\n"));
    };

    function numOrUndef(e) { var v = parseFloat(e.text); return isNaN(v) ? undefined : v; }
    addPivot.onClick = function () {
      addJoint("pivot", { lower: numOrUndef(jLower), upper: numOrUndef(jUpper) });
    };
    addDist.onClick = function () {
      var hz = numOrUndef(jHz), dp = numOrUndef(jDamp);
      if (hz !== undefined) hz = Math.max(0, hz);
      if (dp !== undefined) dp = Math.max(0, Math.min(1, dp));
      addJoint("distance", { hz: hz, damping: dp });
    };
    addSpring.onClick = function () {
      // blank fields use the spring defaults (1.5 Hz, damping 0.1)
      var hz = numOrUndef(jHz), dp = numOrUndef(jDamp);
      if (hz !== undefined) hz = Math.max(0.1, hz);
      if (dp !== undefined) dp = Math.max(0, Math.min(1, dp));
      addJoint("spring", { hz: hz, damping: dp });
    };
    addWeld.onClick = function () {
      // blank Hz = fully rigid weld; a Hz value lets the bond flex
      var hz = numOrUndef(jHz), dp = numOrUndef(jDamp);
      if (hz !== undefined) hz = Math.max(0, hz);
      if (dp !== undefined) dp = Math.max(0, Math.min(1, dp));
      addJoint("weld", { hz: hz, damping: dp });
    };
    addPiston.onClick = function () {
      // limits are in px along the slide axis (0 = start position); axis = rotation of the lower layer
      var sp = numOrUndef(jSpeed), ac = numOrUndef(jAccel);
      if (ac !== undefined) ac = Math.max(0, ac);
      addJoint("piston", { lower: numOrUndef(jLower), upper: numOrUndef(jUpper), speed: sp, accel: ac });
    };
    rmJoints.onClick = function () { removeJoints(); };

    rGo.onClick = function () {
      var names = ["bounce", "friction", "density", "gravity"];
      var idx = rProp.selection ? rProp.selection.index : 0;
      randomizeSelected(names[idx], num(rMin, 0), num(rMax, 1));
    };

    win.layout.layout(true);
    win.onResizing = win.onResize = function () { this.layout.resize(); };
    return win;
  }

  var ui = buildUI(thisObj);
  if (ui instanceof Window) { ui.center(); ui.show(); }

})(this);
