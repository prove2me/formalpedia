-- Prove2me | Theorems.Thm_ProbabilityTheory_ConvolutionSemigroup_leanlevy_chat33_exists_largeUpperMulBCF
-- name    : ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat33_exists_largeUpperMulBCF
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T07:27:44.673642+00:00
-- url     : https://prove2.me/theorems/22c7d2b3-01c4-47d0-8e63-80942e4e6c00
-- title:
--   Bounded continuous upper cutoff multiplied by a bounded continuous function
-- statement:
--   Source-exact bounded continuous upper cutoff product, with uniform bound, used by the Lévy large-set epsilon/three argument.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyKhintchineProof.lean#L3342-L3378

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat33_exists_largeUpperMulBCF (ρ : ℝ) (hρ : 0 < ρ) (n : ℕ)
    (g : ℝ → ℝ) (hg_cont : Continuous g) (M : ℝ)
    (hg_bnd : ∀ x, |g x| ≤ M) :
    ∃ f : BoundedContinuousFunction ℝ ℝ,
      (∀ x, f x = min 1 (max 0 ((|x| - ρ) * ((n + 1 : ℝ) / ρ) + 1)) * g x) ∧
      (∀ x, |f x| ≤ M) := by sorry
