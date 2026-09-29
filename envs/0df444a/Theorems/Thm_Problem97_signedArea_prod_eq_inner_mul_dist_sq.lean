-- Prove2me | Theorems.Thm_Problem97_signedArea_prod_eq_inner_mul_dist_sq
-- name    : Problem97.signedArea_prod_eq_inner_mul_dist_sq
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-08T01:51:15.736717+00:00
-- url     : https://prove2.me/theorems/ae2445f7-f7f6-4401-9b7a-b589d976ef4c
-- title:
--   Signed-Area Product Formula for a Perpendicular-Bisector Point
-- statement:
--   For planar points O,a,b,c with a and b having equal squared distance from O, the product signedArea2(O,a,b)·signedArea2(c,a,b) equals the squared chord length ‖a−b‖² times the inner product of midpoint(a,b)−O with midpoint(a,b)−c.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/blob/88d43fbd49e26dd52753787835044facf1ed91e5/prove2me/submissions/counting-transfer/platform/Theorems/Thm_Problem97_signedArea_prod_eq_inner_mul_dist_sq.lean#L1-L59

/- Generated theorem stub from Erdos9796Proof.P97.CircumcenterSide by Stage 2 proof cut; source SHA-256 29ad9a32acf8129d66c4663579b3568047794eff971aa9120aac73db7971f861 -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_Foundation
import Mathlib.Analysis.InnerProductSpace.Basic
open Problem97



/-!
# Circumcenter-side characterization for non-obtuse inscribed triangles

Three points `a, b, c` on a Euclidean sphere of center `O` form a non-obtuse
triangle iff the smallest enclosing disk of `{a, b, c}` is the sphere itself.
Geometrically this puts the circumcenter `O` inside (or on the boundary of)
the triangle, which downstream consumers use through the signed-area form:
for each chord (say `ab`), the third vertex `c` and the center `O` lie on
the same closed half-plane.

The forward direction is captured by `center_same_side_as_apex_of_nonobtuse`:
if the interior angle of the triangle at `c` is non-obtuse — i.e.,
`⟪a - c, b - c⟫_ℝ ≥ 0` — then `signedArea2 O a b * signedArea2 c a b ≥ 0`.

The proof reduces to a single algebraic identity. With
`m := midpoint ℝ a b` and assuming the perpendicular-bisector condition
`‖a - O‖ = ‖b - O‖` (automatic from the sphere hypothesis):

  `signedArea2 O a b * signedArea2 c a b
      = ⟪m - O, m - c⟫_ℝ * ‖a - b‖²`.

The right-hand side is the product of a sphere-shaped quantity that the
inscribed-angle lemma `inner_chord_eq_two_mul_inner_midpoint` converts to
`(1/2) · ⟪a - c, b - c⟫_ℝ`, and a manifestly non-negative scalar `‖a - b‖²`.
Together with the hypothesis `⟪a - c, b - c⟫_ℝ ≥ 0`, this gives the result.

The companion `signedArea_prod_eq_inner_mul_dist_sq` is the abstract identity
without the inner-product hypothesis on `c`; it depends only on the
perpendicular-bisector condition on `O`. We also expose a `‖·‖²` form
(`signedArea_prod_eq_inner_mul_dist_sq`) that is more convenient for direct
algebraic chaining than re-deriving it from scratch.
-/

open scoped EuclideanGeometry InnerProductSpace

theorem Problem97.signedArea_prod_eq_inner_mul_dist_sq
    (O a b c : ℝ²)
    (hperp : ‖a - O‖ ^ 2 = ‖b - O‖ ^ 2) :
    signedArea2 O a b * signedArea2 c a b =
      ⟪midpoint ℝ a b - O, midpoint ℝ a b - c⟫_ℝ * ‖a - b‖ ^ 2 := by sorry
