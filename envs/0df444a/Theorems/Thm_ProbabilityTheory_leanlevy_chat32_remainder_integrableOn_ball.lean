-- Prove2me | Theorems.Thm_ProbabilityTheory_leanlevy_chat32_remainder_integrableOn_ball
-- name    : ProbabilityTheory.leanlevy_chat32_remainder_integrableOn_ball
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T23:54:25.392191+00:00
-- url     : https://prove2.me/theorems/109d3c93-5a55-4e3b-9944-5c19085b6da2
-- title:
--   Small-ball integrability of the cubic exponential remainder
-- statement:
--   The characteristic cubic Taylor remainder is integrable on the finite-measure unit-radius ball by clamping and a uniform majorant.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyKhintchineProof.lean#L4135-L4159

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Theorems.Thm_ProbabilityTheory_leanlevy_chat32_remainder_clamp_continuous
import Theorems.Thm_ProbabilityTheory_leanlevy_chat32_clamp_eq_of_abs_lt
import Theorems.Thm_ProbabilityTheory_leanlevy_chat32_remainder_clamp_norm_le
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem ProbabilityTheory.leanlevy_chat32_remainder_integrableOn_ball {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (ξ : ℝ) (m : Measure ℝ) [IsFiniteMeasure m] :
    IntegrableOn
      (fun x : ℝ => exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I + ((↑x : ℂ) * ↑ξ) ^ 2 / 2)
      {x : ℝ | |x| < r} m := by sorry
