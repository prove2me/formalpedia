-- Prove2me | Theorems.Thm_ProbabilityTheory_ConvolutionSemigroup_leanlevy_chat32_exists_annulusBCF
-- name    : ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat32_exists_annulusBCF
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T00:20:41.355698+00:00
-- url     : https://prove2.me/theorems/45ac1850-fae8-4686-8e3e-e9d5fed66c40
-- title:
--   Existence of source-exact largeAnnulusBCF smooth bounded cutoff
-- statement:
--   Construct the smooth bounded continuous largeAnnulusBCF cutoff with the exact upstream pointwise formula.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyKhintchineProof.lean#L3221-L3241

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat32_exists_annulusBCF (ρ : ℝ) (hρ : 0 < ρ) (n : ℕ) :
    ∃ f : BoundedContinuousFunction ℝ ℝ,
      ∀ x, f x = max 0 (1 - ((n + 1 : ℝ) / ρ) * max 0 (|(|x| - ρ)| - ρ/(n + 1 : ℝ))) := by sorry
