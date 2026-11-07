-- Prove2me | Theorems.Thm_PredAdvice_routing_rules
-- name    : PredAdvice.routing_rules
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:36:57.096816+00:00
-- url     : https://prove2.me/theorems/856b2c70-cea5-4613-a265-11192cefc6ce
-- title:
--   Proof of Theorem 1.1 — the routing rules forward along a shortest path
-- statement:
--   Let $T^-$ be a shortest-path tree directed toward its root $x$ and $T^+$ one directed away from its root $y$, with $x=y$ or $(x,y)\in E$, $u\in V(T^-)$, $v\in V(T^+)$, $v$ reachable from $u$ and
--   $$
--   \mathrm{dist}(u,x)+\mathbf 1_{x\ne y}+\mathrm{dist}(y,v)=\mathrm{dist}(u,v).
--   $$
--   Let $w_0=u$ and let $w_{k+1}$ be obtained from $w_k$ by one forwarding step (rules 1–3). Then $w_{\mathrm{dist}(u,v)}=v$, and for every $k<\mathrm{dist}(u,v)$: $w_k\ne v$, $(w_k,w_{k+1})\in E$ and $\mathrm{dist}(w_{k+1},v)+1=\mathrm{dist}(w_k,v)$.
--
--   So the three rules, which read only the two trees, the destination and the current vertex, route along a shortest $u$–$v$ path.
--
--   Differences from the source:
--   - encoding: starting at u, each forwarding step decreases the distance to v by one → the k-th iterate of the forwarding step, for k < dist(u, v), and arrival at v after dist(u, v) steps; reason: the route as an iteration; routing stops at v
--   - generalization: the trees T⁻, T⁺ and roots x, y that Lemma 4.4 supplies for (u, v) → any toward tree T⁻ and away tree T⁺ with Lemma 4.4's path guarantee for (u, v); reason: the argument uses only that guarantee; Lemma 4.4's trees are one instance
--   - generalization: a directed unweighted graph (simple, p.6) → Mathlib's Digraph on a finite vertex type, which may have loops; reason: loops never lie on shortest walks and change no distance; loopless digraphs on n vertices are the special case
-- source:
--   Kopelowitz, Korin, Roditty, Using Small Advice to Compress the Predecessor Matrix, STOC 2027 submission (manuscript sha256 0ae8a68d…), proof of Theorem 1.1, p.24

import Mathlib
import Definitions.Def_PredAdvice_routeStep

set_option autoImplicit false

namespace PredAdvice

/-- **The routing rules** (proof of Theorem 1.1, Kopelowitz, Korin, Roditty, *Using Small Advice to Compress the Predecessor Matrix*, STOC 2027 submission (manuscript sha256 0ae8a68d…), p.24). Let `T⁻` be a shortest-path tree
directed toward its root `x` and `T⁺` one directed away from its root `y`, with `x = y` or
`(x, y) ∈ E`, `u ∈ V(T⁻)`, `v ∈ V(T⁺)` and `dist(u, x) + 1_{x≠y} + dist(y, v) = dist(u, v) < ∞`, so
that the `u–x` path in `T⁻`, the edge `(x, y)` when `x ≠ y` and the `y–v` path in `T⁺` form a
shortest `u–v` path `P` (Lemma 4.4). Applying rules 1–3 (`routeStep`) repeatedly from `u`, each
forwarding step follows an edge and decreases the distance to `v` by one, and `v` is reached after
exactly `dist(u, v)` steps.

**Formalization Note** The `k`-th vertex of the route is `routeStep^[k] u`. Routing stops at `v`, so
the step clauses are stated for `k < dist(u, v)` (where the current vertex is not `v`). -/
theorem routing_rules :
    ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : Digraph V) (Tm Tp : RootedTree V) (u v : V),
      IsTowardTree G Tm → IsAwayTree G Tp → (Tm.root = Tp.root ∨ G.Adj Tm.root Tp.root) →
      u ∈ Tm.verts → v ∈ Tp.verts → Reachable G u v →
      dist G u Tm.root + (if Tm.root = Tp.root then 0 else 1) + dist G Tp.root v = dist G u v →
      (routeStep Tm Tp v)^[(dist G u v).toNat] u = v ∧
      ∀ k : ℕ, k < (dist G u v).toNat →
        (routeStep Tm Tp v)^[k] u ≠ v ∧
        G.Adj ((routeStep Tm Tp v)^[k] u) ((routeStep Tm Tp v)^[k + 1] u) ∧
        dist G ((routeStep Tm Tp v)^[k + 1] u) v + 1 = dist G ((routeStep Tm Tp v)^[k] u) v := by sorry

end PredAdvice
