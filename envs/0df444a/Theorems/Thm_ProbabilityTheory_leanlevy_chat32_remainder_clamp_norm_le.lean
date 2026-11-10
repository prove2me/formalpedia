-- Prove2me | Theorems.Thm_ProbabilityTheory_leanlevy_chat32_remainder_clamp_norm_le
-- name    : ProbabilityTheory.leanlevy_chat32_remainder_clamp_norm_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T23:42:13.494362+00:00
-- url     : https://prove2.me/theorems/89f4bf6c-eeff-45bb-b61e-0995bb13236e
-- title:
--   Clamped cubic remainder has a constant majorant
-- statement:
--   Clamped cubic remainder has a constant majorant
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyKhintchineProof.lean#L4123-L4132

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Theorems.Thm_ProbabilityTheory_leanlevy_chat31_smallBall_remainder_continuous
import Theorems.Thm_ProbabilityTheory_leanlevy_chat31_smallBall_remainder_norm_le_crude
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem ProbabilityTheory.leanlevy_chat32_remainder_clamp_norm_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (ξ x : ℝ) :
    ‖(fun y : ℝ => exp ((↑y : ℂ) * ↑ξ * I) - 1 - (↑y : ℂ) * ↑ξ * I + ((↑y : ℂ) * ↑ξ) ^ 2 / 2)
        (max (-r) (min x r))‖ ≤ 2 + |ξ| + ξ ^ 2 / 2 := by sorry
