-- Prove2me | Theorems.Thm_Problem97_inner_chord_eq_two_mul_inner_midpoint
-- name    : Problem97.inner_chord_eq_two_mul_inner_midpoint
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-08T01:49:40.227869+00:00
-- url     : https://prove2.me/theorems/56380a12-6784-443d-b4be-976beaaed01a
-- title:
--   On-Sphere Chord-Midpoint Inner-Product Identity
-- statement:
--   Let O,c,x,y be points in the Euclidean plane with x, y, and c at the same distance from O. Then the inner product of x−c and y−c equals twice the inner product of midpoint(x,y)−O and midpoint(x,y)−c.
-- source:
--   https://github.com/mysticflounder/erdos-97-96-formalization/blob/88d43fbd49e26dd52753787835044facf1ed91e5/prove2me/submissions/counting-transfer/platform/Theorems/Thm_Problem97_inner_chord_eq_two_mul_inner_midpoint.lean#L1-L46

/- Generated theorem stub from Erdos9796Proof.P97.Cap.ArcInscribedAngle by Stage 2 proof cut; source SHA-256 229631a65f8abd10a13cc09e09bfa34327c4b03427c96d3053e9f4b1fef392da -/
import Definitions.Def_Erdos9796Counting_Adapter
import Definitions.Def_Erdos9796Counting_Foundation
import Mathlib.Analysis.InnerProductSpace.Basic
open Problem97



/-!
# On-sphere chord-arc inner-product nonnegativity

For three points `c, x, y` on a 2D Euclidean sphere of center `O` and radius
`r`, if `c` lies on the closed half-plane of the chord `xy` containing `O`,
then the inscribed angle at `c` subtending `xy` is at most `π/2`; equivalently
`⟪x - c, y - c⟫_ℝ ≥ 0`.

This is the inscribed-angle / Thales-style step of the MEC arc-angle chain:
once `c` is pinned to the major-arc side (the half-plane of `xy` containing
the center `O`), the inner-product nonnegativity feeds the algebraic step
`Problem97.dist_midpoint_ge_half_of_inner_nn` to close the on-sphere version
of the cap-arc midpoint inequality.

The proof reduces the inscribed-angle theorem to a clean algebraic identity:
under the sphere hypothesis `‖x - O‖ = ‖y - O‖ = ‖c - O‖`, one has

  `⟪x - c, y - c⟫_ℝ = 2 · ⟪m - O, m - c⟫_ℝ`,

where `m := midpoint ℝ x y`.  The right-hand side is `≥ 0` exactly when `c`
lies in the closed half-plane of the chord `xy` containing the center — the
chord-side characterization of the major arc.
-/

open scoped EuclideanGeometry InnerProductSpace

theorem Problem97.inner_chord_eq_two_mul_inner_midpoint
    {O c x y : ℝ²}
    (hxO : ‖x - O‖ = ‖c - O‖) (hyO : ‖y - O‖ = ‖c - O‖) :
    ⟪x - c, y - c⟫_ℝ =
      2 * ⟪midpoint ℝ x y - O, midpoint ℝ x y - c⟫_ℝ := by sorry
