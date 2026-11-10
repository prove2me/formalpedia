-- Prove2me | Theorems.Thm_ProbabilityTheory_ConvolutionSemigroup_leanlevy_chat32_annulusRamp_tendsto_indicator
-- name    : ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat32_annulusRamp_tendsto_indicator
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T00:35:30.230123+00:00
-- url     : https://prove2.me/theorems/f78d329a-0a00-422e-b331-ce3c284a7ba0
-- title:
--   Annulus ramp converges to boundary-shell indicator
-- statement:
--   Pointwise convergence of a narrow smooth annular ramp to the indicator of the null boundary shell.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyKhintchineProof.lean#L3310-L3341

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat32_annulusRamp_tendsto_indicator (ρ : ℝ) (hρ : 0 < ρ) (x : ℝ) :
    Tendsto (fun n : ℕ => max 0 (1 - ((n + 1 : ℝ) / ρ) * max 0 (|(|x| - ρ)| - ρ / (n + 1 : ℝ)))) atTop
      (𝓝 (Set.indicator {y : ℝ | |y| = ρ} (fun _ => (1 : ℝ)) x)) := by sorry
