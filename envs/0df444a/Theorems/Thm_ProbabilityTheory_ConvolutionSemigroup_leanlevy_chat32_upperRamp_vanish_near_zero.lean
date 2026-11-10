-- Prove2me | Theorems.Thm_ProbabilityTheory_ConvolutionSemigroup_leanlevy_chat32_upperRamp_vanish_near_zero
-- name    : ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat32_upperRamp_vanish_near_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-11-10T00:28:30.592411+00:00
-- url     : https://prove2.me/theorems/c2dc1d52-a0d2-4afe-992e-91245f48f1ae
-- title:
--   leanlevy_chat32_upperRamp_vanish_near_zero
-- statement:
--   Exact source smooth cutoff uniform range or vanishing near the origin.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyKhintchineProof.lean#L3138-L3192

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat32_upperRamp_vanish_near_zero (ρ : ℝ) (hρ : 0 < ρ) (n : ℕ) (hn : 1 ≤ n) :
    ∃ r > (0 : ℝ), ∀ x, |x| < r → min 1 (max 0 ((|x| - ρ) * ((n + 1 : ℝ) / ρ) + 1)) = 0 := by sorry
