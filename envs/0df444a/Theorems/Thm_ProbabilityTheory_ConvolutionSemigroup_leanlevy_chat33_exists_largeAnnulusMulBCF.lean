-- Prove2me | Theorems.Thm_ProbabilityTheory_ConvolutionSemigroup_leanlevy_chat33_exists_largeAnnulusMulBCF
-- name    : ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat33_exists_largeAnnulusMulBCF
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T07:29:36.711367+00:00
-- url     : https://prove2.me/theorems/499e8955-5399-48e2-8c45-9062d403455a
-- title:
--   Bounded continuous annulus cutoff multiplied by bounded continuous function
-- statement:
--   Source-exact bounded continuous annulus cutoff product and uniform bound from the original Lévy large-set argument.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyKhintchineProof.lean#L3379-L3417

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat33_exists_largeAnnulusMulBCF (ρ : ℝ) (hρ : 0 < ρ) (n : ℕ)
    (g : ℝ → ℝ) (hg_cont : Continuous g) (M : ℝ)
    (hg_bnd : ∀ x, |g x| ≤ M) :
    ∃ f : BoundedContinuousFunction ℝ ℝ,
      (∀ x, f x = max 0 (1 - ((n + 1 : ℝ) / ρ) * max 0 (|(|x| - ρ)| - ρ/(n + 1 : ℝ))) * g x) ∧
      (∀ x, |f x| ≤ M) := by sorry
