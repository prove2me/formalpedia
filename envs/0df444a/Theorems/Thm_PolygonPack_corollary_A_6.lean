-- Prove2me | Theorems.Thm_PolygonPack_corollary_A_6
-- name    : PolygonPack.corollary_A_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:58:14.98874+00:00
-- url     : https://prove2.me/theorems/9b746fbb-54c5-4e8b-b2a5-b0ac7a820a00
-- title:
--   Corollary A.6 — exceptional Tight polygons
-- statement:
--   Let $0<c\le1/400$, $a_0>0$, and let $h_0=2a_0$ satisfy $h_0\le\min\{c/400,\,1/(500K),\,1/(300LK),\,1/16\}$. If all polygons of a feasible subset of a valid instance lie in $T^0$, then that subset has at most two elements.
--
--   Together with an area bound on Large polygons, this makes the exceptional class small enough for exact enumeration.
--
--   Differences from the source:
--   - reading: the above knapsack cutoffs → the hypotheses of Lemma A.5 with t = 0: c ≤ 1/400, and the cutoff on h0 = 2·a0; reason: the proof uses "the Tight-only result with t = 0"
--   - generalization: convex polygons given by their vertices → the convex hull of any finite rational vertex list, in any order; reason: the vertices of a convex polygon are such a list
-- source:
--   Khan, Mathur, Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons, STOC 2027 submission (manuscript sha256 7a527fb3…), Corollary A.6, p.28

import Mathlib
import Definitions.Def_PolygonPack_Instance
import Definitions.Def_PolygonPack_Pose
import Definitions.Def_PolygonPack_Packs
import Definitions.Def_PolygonPack_Instance_Valid
import Definitions.Def_PolygonPack_diag
import Definitions.Def_PolygonPack_eucl
import Definitions.Def_PolygonPack_thick
import Definitions.Def_PolygonPack_diamPair
import Definitions.Def_PolygonPack_polyArea
import Definitions.Def_PolygonPack_placedUV
import Definitions.Def_PolygonPack_canonBottom
import Definitions.Def_PolygonPack_IsTight
import Definitions.Def_PolygonPack_Kc

namespace PolygonPack

/-- **Corollary A.6 (Exceptional Tight polygons).** Khan, Mathur, *Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons*, STOC 2027 submission (manuscript sha256 7a527fb3…), p.28. "A feasible square contains at most two Tight polygons with nonpositive canonical
bottom under the above knapsack cutoffs."

**Formalization Note.** "The above knapsack cutoffs" are the hypotheses of Lemma A.5: `c ≤ 1/400` and `h0 = 2·a0 ≤ min{c/400, 1/(500K), 1/(300LK), 1/16}`. -/
theorem corollary_A_6 (c a0 : ℝ) (hc : 0 < c) (hc' : c ≤ 1 / 400) (ha0 : 0 < a0) (hcut : IsA5Cutoff c (2 * a0)) (I : Instance)
    (hI : I.Valid) (S : Finset (Fin I.n)) (hS : Feasible I S) (hT0 : ∀ i ∈ S, IsTZero c a0 (I.verts i)) :
    S.card ≤ 2 := by sorry

end PolygonPack
