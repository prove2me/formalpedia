-- Prove2me | Theorems.Thm_ProbabilityTheory_leanlevy_chat32_remainder_inner_ball_norm_le
-- name    : ProbabilityTheory.leanlevy_chat32_remainder_inner_ball_norm_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T23:47:48.923979+00:00
-- url     : https://prove2.me/theorems/f567c9e3-e6a5-4da7-8caa-9bb3fb8c135d
-- title:
--   Inner-ball cubic remainder bounded by second moment
-- statement:
--   The norm of the small-ball cubic remainder integral is controlled by (2/9)|ξ|³δ times the second moment, given both integrability assumptions.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyKhintchineProof.lean#L4276-L4343

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Theorems.Thm_ProbabilityTheory_leanlevy_chat31_smallBall_remainder_norm_le_cube
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem ProbabilityTheory.leanlevy_chat32_remainder_inner_ball_norm_le {δ : ℝ} (_hδ : 0 < δ) (_hδ1 : δ ≤ 1) (ξ : ℝ) (hδξ : δ * |ξ| ≤ 1)
    (m : Measure ℝ)
    (hRint : IntegrableOn
      (fun x : ℝ => exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I + ((↑x : ℂ) * ↑ξ) ^ 2 / 2)
      {x : ℝ | |x| < δ} m)
    (hsqint : IntegrableOn (fun x : ℝ => x ^ 2) {x : ℝ | |x| < δ} m) :
    ‖∫ x in {x | |x| < δ},
        (exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I + ((↑x : ℂ) * ↑ξ) ^ 2 / 2) ∂m‖ ≤
      (2 / 9 : ℝ) * |ξ| ^ 3 * δ * ∫ x in {x | |x| < δ}, x ^ 2 ∂m := by sorry
