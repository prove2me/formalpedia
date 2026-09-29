-- Prove2me | Theorems.Thm_Problem97_collinear_of_signedArea2_eq_zero
-- name    : Problem97.collinear_of_signedArea2_eq_zero
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-08T02:09:14.667004+00:00
-- url     : https://prove2.me/theorems/42feb980-0605-457b-ab08-b6506f345d57
-- title:
--   Collinearity from Vanishing Signed Area
-- statement:
--   For three points v₁, v₂, v₃ in ℝ², if signedArea2 v₁ v₂ v₃ = 0, then the set {v₁, v₂, v₃} is collinear over ℝ.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/blob/88d43fbd49e26dd52753787835044facf1ed91e5/prove2me/submissions/counting-transfer/platform/Theorems/Thm_Problem97_collinear_of_signedArea2_eq_zero.lean#L1-L67

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

lemma Problem97.collinear_of_signedArea2_eq_zero (v1 v2 v3 : ℝ²)
    (h : signedArea2 v1 v2 v3 = 0) :
    Collinear ℝ ({v1, v2, v3} : Set ℝ²) := by sorry
