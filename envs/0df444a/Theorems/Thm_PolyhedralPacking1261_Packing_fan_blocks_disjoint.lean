-- Prove2me | Theorems.Thm_PolyhedralPacking1261_Packing_fan_blocks_disjoint
-- name    : PolyhedralPacking1261.Packing.fan_blocks_disjoint
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:37:37.682708+00:00
-- url     : https://prove2.me/theorems/7e03db13-3950-481b-b82f-884c41db580f
-- title:
--   Lemma 6 — separation of fan blocks
-- statement:
--   Fix positive b,c and two bc-parallelepipeds satisfying the Section 2 individual-fit assumptions, with integer shadow labels k_i≤k_j. For all integer block labels ell_i<ell_j and all real horizontal offsets x_i,x_j, their translations by (x_i,(ell_i-1+k_i/2)b,0) and (x_j,(ell_j-1+k_j/2)b,0) have disjoint ambient interiors. There is no required horizontal separation. Negative integer labels are allowed.
--
--   Differences from the source: none.
-- source:
--   Simon Bartlmae, Anders Aamand, Mikkel Abrahamsen, Polylogarithmic Approximation for Packing Convex Polyhedra, STOC 2027 submission #1261 (October 2026), canonical PDF SHA-256 b915da2d5fece730ea9946885b05ad09e10e575374e6a1df96e8a6149cb0e67e, Lemma 6, PDF p.8 = printed p.7; standing assumptions §2, PDF pp.6–7

import Definitions.Def_PolyhedralPacking1261_Packing_Parallelepipeds

set_option autoImplicit false

namespace PolyhedralPacking1261.Packing

/-- Lemma 6, PDF p.8 (printed p.7). Block labels are integers, and horizontal
offsets are arbitrary real numbers. There is no horizontal-separation assumption. -/
theorem fan_blocks_disjoint (b c : ℝ) (hb : 0 < b) (hc : 0 < c)
    (p q : BCParameters) (hp : IndividuallyFits b c p) (hq : IndividuallyFits b c q)
    (hshadow : p.k ≤ q.k) (li lj : ℤ) (hblock : li < lj) (xi xj : ℝ) :
    Disjoint
      (interior (shiftSet (fanTranslation b p xi li) (bcBody b c p)))
      (interior (shiftSet (fanTranslation b q xj lj) (bcBody b c q))) := by sorry

end PolyhedralPacking1261.Packing
