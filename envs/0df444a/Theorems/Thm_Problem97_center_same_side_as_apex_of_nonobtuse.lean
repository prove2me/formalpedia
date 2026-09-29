-- Prove2me | Theorems.Thm_Problem97_center_same_side_as_apex_of_nonobtuse
-- name    : Problem97.center_same_side_as_apex_of_nonobtuse
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-08T02:03:16.483314+00:00
-- url     : https://prove2.me/theorems/65adbaf5-af4f-40a5-8c99-c9102a98db01
-- title:
--   A non-obtuse inscribed triangle places the center on the apex side
-- statement:
--   Let $a,b,c$ lie on a circle with center $O$ and radius $r$. If the angle at $c$ is non-obtuse, expressed by $\langle a-c,b-c\rangle\ge 0$, then $$\operatorname{area}_2(O,a,b)\,\operatorname{area}_2(c,a,b)\ge 0.$$ Thus the circumcenter and the apex $c$ lie in the same closed half-plane determined by the chord $ab$, a fact used to orient the three caps.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/blob/88d43fbd49e26dd52753787835044facf1ed91e5/prove2me/submissions/counting-transfer/platform/Theorems/Thm_Problem97_center_same_side_as_apex_of_nonobtuse.lean#L1-L59

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

theorem Problem97.center_same_side_as_apex_of_nonobtuse
    {O a b c : ℝ²} {r : ℝ}
    (haO : ‖a - O‖ = r) (hbO : ‖b - O‖ = r) (hcO : ‖c - O‖ = r)
    (hacuteC : ⟪a - c, b - c⟫_ℝ ≥ 0) :
    signedArea2 O a b * signedArea2 c a b ≥ 0 := by sorry
