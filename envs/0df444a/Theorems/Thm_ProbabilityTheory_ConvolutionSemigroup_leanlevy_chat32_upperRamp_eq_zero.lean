-- Prove2me | Theorems.Thm_ProbabilityTheory_ConvolutionSemigroup_leanlevy_chat32_upperRamp_eq_zero
-- name    : ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat32_upperRamp_eq_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T00:22:58.181649+00:00
-- url     : https://prove2.me/theorems/ee9f5c8c-608f-4bdd-8780-fc7428e42f5b
-- title:
--   leanlevy_chat32_upperRamp_eq_zero
-- statement:
--   Source-exact sharp value of the smooth large-jump cutoff inside/outside the transition band.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyKhintchineProof.lean#L3144-L3179

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat32_upperRamp_eq_zero (ρ : ℝ) (hρ : 0 < ρ) (n : ℕ) (x : ℝ)
    (hx : |x| ≤ ρ - ρ / (n + 1 : ℝ)) : min 1 (max 0 ((|x| - ρ) * ((n + 1 : ℝ) / ρ) + 1)) = 0 := by sorry
