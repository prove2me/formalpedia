-- Prove2me | Theorems.Thm_PlanarMetricElections_Peer_dominance_separation
-- name    : PlanarMetricElections.Peer.dominance_separation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:51:06.205042+00:00
-- url     : https://prove2.me/theorems/1b1e86d7-3a53-438d-b33a-78f995e37fcf
-- title:
--   Lemma 5.1 — dominance separation
-- statement:
--   For any real norm $N$ on the real plane and any two distinct points $a,b$, write $d_N(x,y)=N(x-y)$ and $\operatorname{Dom}_d(a,b)=\{x:d(a,x)<d(b,x)\}$. Then
--
--   $$b\notin\operatorname{conv}(\operatorname{Dom}_{d_N}(a,b)).$$
--
--   For the Manhattan distance $d_1$ there is, in addition, an open axis-parallel half-plane $H$ such that
--
--   $$\operatorname{Dom}_{d_1}(a,b)\subseteq H,\qquad b\notin H.$$
--
--   Both clauses are included. The result supplies the separation property needed for the net-to-game comparison.
--
--   Differences from the source:
--   - encoding: an arbitrary genuine real norm on the plane → a Mathlib real seminorm together with definiteness; reason: these are exactly the norm axioms; no Euclidean or fixed-product-norm restriction is imposed
-- source:
--   Gabriel Morete de Azevedo, Ulysse Hennebelle, STOC 2027 submission #1404 (October 2026), Lemma 5.1, p. 9 (PDF p. 10)

import Definitions.Def_PlanarMetricElections_Peer_Geometry

set_option autoImplicit false
open scoped Classical

namespace PlanarMetricElections.Peer

theorem dominance_separation :
    (∀ (N : PlanarNorm) (a b : Plane), a ≠ b →
      b ∉ convexHull ℝ (dominance (normDistance N) a b)) ∧
    (∀ a b : Plane, a ≠ b → ∃ H : Set Plane,
      IsOpenAxisHalfPlane H ∧ dominance dOne a b ⊆ H ∧ b ∉ H) := by sorry

end PlanarMetricElections.Peer
