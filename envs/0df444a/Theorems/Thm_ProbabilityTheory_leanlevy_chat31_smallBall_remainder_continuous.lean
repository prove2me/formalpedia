-- Prove2me | Theorems.Thm_ProbabilityTheory_leanlevy_chat31_smallBall_remainder_continuous
-- name    : ProbabilityTheory.leanlevy_chat31_smallBall_remainder_continuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T22:45:21.553205+00:00
-- url     : https://prove2.me/theorems/46764a62-d8a9-49fc-a5b0-20ceac3f259f
-- title:
--   Continuity of the cubic characteristic-exponent remainder
-- statement:
--   The third-order complex exponential remainder R(ξ,x)=exp(i ξ x)-1-i ξ x+(ξ x)^2/2 is continuous as a function of the real jump size x.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyKhintchineProof.lean#L4050-L4060

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem ProbabilityTheory.leanlevy_chat31_smallBall_remainder_continuous (ξ : ℝ) :
    Continuous (fun x : ℝ =>
      exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I
        + ((↑x : ℂ) * ↑ξ) ^ 2 / 2) := by sorry
