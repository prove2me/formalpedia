-- Prove2me | Theorems.Thm_ProbabilityTheory_leanlevy_chat31_smallBall_remainder_norm_le_cube
-- name    : ProbabilityTheory.leanlevy_chat31_smallBall_remainder_norm_le_cube
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T22:52:11.151949+00:00
-- url     : https://prove2.me/theorems/70178c3e-3e58-4e6f-9dfe-c1eaf78fc2f7
-- title:
--   Cubic bound for the small-jump characteristic-exponent remainder
-- statement:
--   At |xξ|≤1, the complex third-order Taylor remainder is bounded by (2/9)|ξ|^3|x|^3. This is the small-jump cutoff estimate for the Lévy-Khintchine exponent limit.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyKhintchineProof.lean#L4096-L4110

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem ProbabilityTheory.leanlevy_chat31_smallBall_remainder_norm_le_cube
    {ξ x : ℝ} (hxξ : |x * ξ| ≤ 1) :
    ‖exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I
      + ((↑x : ℂ) * ↑ξ) ^ 2 / 2‖ ≤
      (2 / 9 : ℝ) * |ξ| ^ 3 * |x| ^ 3 := by sorry
