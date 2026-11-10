-- Prove2me | Theorems.Thm_ProbabilityTheory_leanlevy_chat32_remainder_clamp_continuous
-- name    : ProbabilityTheory.leanlevy_chat32_remainder_clamp_continuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T23:42:14.80607+00:00
-- url     : https://prove2.me/theorems/7a8da8ee-4573-4354-a2a9-6b302b88a4a9
-- title:
--   Clamped cubic remainder is continuous
-- statement:
--   Clamped cubic remainder is continuous
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyKhintchineProof.lean#L4111-L4116

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Theorems.Thm_ProbabilityTheory_leanlevy_chat31_smallBall_remainder_continuous
import Theorems.Thm_ProbabilityTheory_leanlevy_chat31_smallBall_remainder_norm_le_crude
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem ProbabilityTheory.leanlevy_chat32_remainder_clamp_continuous (r : ℝ) (ξ : ℝ) :
    Continuous (fun x : ℝ =>
      (fun y : ℝ => exp ((↑y : ℂ) * ↑ξ * I) - 1 - (↑y : ℂ) * ↑ξ * I + ((↑y : ℂ) * ↑ξ) ^ 2 / 2)
        (max (-r) (min x r))) := by sorry
