-- Prove2me | Theorems.Thm_ProbabilityTheory_ConvolutionSemigroup_leanlevy_chat32_upperRamp_eq_one
-- name    : ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat32_upperRamp_eq_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T00:22:58.605982+00:00
-- url     : https://prove2.me/theorems/7ea3e01d-01f0-4387-bd60-0de69bba340b
-- title:
--   leanlevy_chat32_upperRamp_eq_one
-- statement:
--   Source-exact sharp value of the smooth large-jump cutoff inside/outside the transition band.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyKhintchineProof.lean#L3144-L3179

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat32_upperRamp_eq_one (ρ : ℝ) (hρ : 0 < ρ) (n : ℕ) (x : ℝ)
    (hx : ρ ≤ |x|) : min 1 (max 0 ((|x| - ρ) * ((n + 1 : ℝ) / ρ) + 1)) = 1 := by sorry
