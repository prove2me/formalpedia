-- Prove2me | Theorems.Thm_Problem97_signedArea2_eq_zero_exists_smul
-- name    : Problem97.signedArea2_eq_zero_exists_smul
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-08T01:59:48.277981+00:00
-- url     : https://prove2.me/theorems/021f53de-8f02-48d9-b4c1-e975220b53a9
-- title:
--   Vanishing signed area gives a scalar collinearity witness
-- statement:
--   Let $v_1,v_2,v_3$ be planar points with $v_2\ne v_1$. If their doubled signed area is zero, then there is a real scalar $r$ such that $$v_3-v_1=r(v_2-v_1).$$ This coordinate lemma supplies an explicit linear-dependence witness used in the nondegeneracy layer.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/blob/88d43fbd49e26dd52753787835044facf1ed91e5/prove2me/submissions/counting-transfer/platform/Theorems/Thm_Problem97_signedArea2_eq_zero_exists_smul.lean#L1-L67

/- Generated theorem stub from Erdos9796Proof.P97.Moser.NonDeg by Stage 2 proof cut; source SHA-256 dd0335fd4a8de1d4d259bdc5a1fcac46e7a179fe1304481d159a516764ebdac7 -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_Foundation
open Problem97



/-!
# Moser triangle vertices are noncollinear: nonzero signed area

The circumscribed branch of `Problem97.MEC.MoserTriangle` carries three
pairwise distinct `A`-vertices on the MEC boundary. This file proves that
those three vertices have nonzero `signedArea2`, which the downstream
cap-partition consumer (`Problem97.MEC.cap_partition_from_moser_circumscribed`)
needs to discharge its `hMoserNonDeg` hypothesis.

## Mathematical content

Three distinct points equidistant from a common center cannot be
collinear: a line meets a circle in at most two points. We package
this via Mathlib's strict-convex-space machinery:

* If three collinear points lie on a circle, one is `Wbtw` of the other
  two by `Collinear.wbtw_or_wbtw_or_wbtw`. With pairwise distinctness
  this strengthens to `Sbtw`, and `Sbtw.dist_lt_max_dist` gives a
  strictly smaller distance to the center — contradicting equidistance.

To translate to `signedArea2`, we prove
`signedArea2 v1 v2 v3 = 0 → Collinear ℝ {v1, v2, v3}` directly from the
2D cross-product identity (case analysis on which coordinate of
`v2 - v1` is nonzero, picking the scalar accordingly).

## Main declarations

* `Problem97.collinear_of_signedArea2_eq_zero` — algebraic predicate
  `signedArea2 = 0` implies the three points are collinear.
* `Problem97.MEC.not_collinear_of_three_dist_eq` — three distinct
  equidistant points are noncollinear (uses `StrictConvexSpace ℝ ℝ²`).
* `Problem97.MEC.signedArea2_ne_zero_of_three_dist_eq` — combining the
  two: three distinct equidistant points have nonzero signed area.
* `Problem97.MEC.moser_triangle_signed_area_ne_zero` — the target
  theorem applied to the circumscribed branch of `MoserTriangle`.
-/

open scoped EuclideanGeometry
open Finset

lemma Problem97.signedArea2_eq_zero_exists_smul {v1 v2 v3 : ℝ²}
    (h21 : v2 ≠ v1) (h : signedArea2 v1 v2 v3 = 0) :
    ∃ r : ℝ, v3 - v1 = r • (v2 - v1) := by sorry
