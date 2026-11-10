-- Prove2me | Theorems.Thm_ProbabilityTheory_ConvolutionSemigroup_leanlevy_chat32_exists_upperBCF
-- name    : ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat32_exists_upperBCF
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T00:20:39.888946+00:00
-- url     : https://prove2.me/theorems/adac0cc5-9348-4b43-b9cb-c1f3a9a62bc8
-- title:
--   Existence of source-exact largeUpperBCF smooth bounded cutoff
-- statement:
--   Construct the smooth bounded continuous largeUpperBCF cutoff with the exact upstream pointwise formula.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyKhintchineProof.lean#L3121-L3142

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat32_exists_upperBCF (ρ : ℝ) (hρ : 0 < ρ) (n : ℕ) :
    ∃ f : BoundedContinuousFunction ℝ ℝ,
      ∀ x, f x = min 1 (max 0 ((|x| - ρ) * ((n + 1 : ℝ) / ρ) + 1)) := by sorry
