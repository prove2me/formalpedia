-- Prove2me | Theorems.Thm_PolyhedralPacking1261_Packing_same_shadow_separation
-- name    : PolyhedralPacking1261.Packing.same_shadow_separation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:37:34.945364+00:00
-- url     : https://prove2.me/theorems/e4630f00-d6af-4ca2-a1ed-98a20f7a20af
-- title:
--   Lemma 5 — same-shadow separation if and only if
-- statement:
--   Fix positive b,c and two centered bc-parallelepipeds satisfying all Section 2 individual-fit assumptions. If their integer shadow labels agree, then for every real h the first and the second translated by (h,0,0) have disjoint ambient interiors if and only if |h|≥(a_i+a_j+|u_i-u_j|+|v_i-v_j|)/2. Equality allows boundary contact. Parameter records may coincide, so repeated pieces and zero shear distances are retained.
--
--   Differences from the source: none.
-- source:
--   Simon Bartlmae, Anders Aamand, Mikkel Abrahamsen, Polylogarithmic Approximation for Packing Convex Polyhedra, STOC 2027 submission #1261 (October 2026), canonical PDF SHA-256 b915da2d5fece730ea9946885b05ad09e10e575374e6a1df96e8a6149cb0e67e, Lemma 5, PDF p.7 = printed p.6; standing assumptions §2, PDF pp.6–7

import Definitions.Def_PolyhedralPacking1261_Packing_Parallelepipeds

set_option autoImplicit false

namespace PolyhedralPacking1261.Packing

/-- Lemma 5, PDF p.7 (printed p.6), including both directions and equality
at boundary contact. The Section 2 individual-fit assumptions are retained. -/
theorem same_shadow_separation (b c : ℝ) (hb : 0 < b) (hc : 0 < c)
    (p q : BCParameters) (hp : IndividuallyFits b c p) (hq : IndividuallyFits b c q)
    (hshadow : p.k = q.k) (h : ℝ) :
    Disjoint (interior (bcBody b c p))
      (interior (shiftSet ![h, 0, 0] (bcBody b c q))) ↔
    |h| ≥ (p.a + q.a + shearDistance p q) / 2 := by sorry

end PolyhedralPacking1261.Packing
