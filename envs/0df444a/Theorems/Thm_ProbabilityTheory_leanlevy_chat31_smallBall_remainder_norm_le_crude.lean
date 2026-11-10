-- Prove2me | Theorems.Thm_ProbabilityTheory_leanlevy_chat31_smallBall_remainder_norm_le_crude
-- name    : ProbabilityTheory.leanlevy_chat31_smallBall_remainder_norm_le_crude
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T22:46:42.034796+00:00
-- url     : https://prove2.me/theorems/141ccad5-4477-4b63-aefa-ac41ff60f556
-- title:
--   Uniform unit-ball bound for the cubic characteristic remainder
-- statement:
--   On the unit ball, the modulus of the cubic complex exponential remainder is at most 2 + |ξ| + ξ²/2. This provides an integrable constant majorant after clamping.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyKhintchineProof.lean#L4060-L4095

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem ProbabilityTheory.leanlevy_chat31_smallBall_remainder_norm_le_crude
    {ξ x : ℝ} (hx : |x| ≤ 1) :
    ‖exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I
      + ((↑x : ℂ) * ↑ξ) ^ 2 / 2‖ ≤ 2 + |ξ| + ξ ^ 2 / 2 := by sorry
