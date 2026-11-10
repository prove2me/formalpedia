-- Prove2me | Theorems.Thm_ProbabilityTheory_ConvolutionSemigroup_leanlevy_chat32_upperRamp_tendsto_indicator
-- name    : ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat32_upperRamp_tendsto_indicator
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T00:24:06.181269+00:00
-- url     : https://prove2.me/theorems/418fbb65-263c-4e63-b11a-a9161334bf8f
-- title:
--   Smooth upper ramp tends pointwise to large-set indicator
-- statement:
--   Pointwise convergence of the smooth upper ramp to the indicator of large jumps.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyKhintchineProof.lean#L3193-L3228

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat32_upperRamp_tendsto_indicator (ρ : ℝ) (hρ : 0 < ρ) (x : ℝ) :
    Tendsto (fun n : ℕ => min 1 (max 0 ((|x| - ρ) * ((n + 1 : ℝ) / ρ) + 1))) atTop
      (𝓝 (Set.indicator {y : ℝ | ρ ≤ |y|} (fun _ => (1 : ℝ)) x)) := by sorry
