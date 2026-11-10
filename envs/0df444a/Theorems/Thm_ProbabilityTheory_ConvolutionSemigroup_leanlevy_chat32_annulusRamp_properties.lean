-- Prove2me | Theorems.Thm_ProbabilityTheory_ConvolutionSemigroup_leanlevy_chat32_annulusRamp_properties
-- name    : ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat32_annulusRamp_properties
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T00:29:46.081715+00:00
-- url     : https://prove2.me/theorems/eac75340-6fca-4cf5-b65c-0f9ddc7c4ff4
-- title:
--   Source-exact annular cutoff range and plateau properties
-- statement:
--   The source annular cutoff remains between zero and one, is identically one on the inner annular plateau and zero off the outer annulus.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyKhintchineProof.lean#L3249-L3286

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat32_annulusRamp_properties (ρ : ℝ) (hρ : 0 < ρ) (n : ℕ) :
    (∀ x : ℝ, 0 ≤ max 0 (1 - ((n + 1 : ℝ) / ρ) * max 0 (|(|x| - ρ)| - ρ / (n + 1 : ℝ))) ∧ max 0 (1 - ((n + 1 : ℝ) / ρ) * max 0 (|(|x| - ρ)| - ρ / (n + 1 : ℝ))) ≤ 1) ∧
    (∀ x : ℝ, |(|x| - ρ)| ≤ ρ / (n + 1 : ℝ) → max 0 (1 - ((n + 1 : ℝ) / ρ) * max 0 (|(|x| - ρ)| - ρ / (n + 1 : ℝ))) = 1) ∧
    (∀ x : ℝ, 2 * ρ / (n + 1 : ℝ) ≤ |(|x| - ρ)| → max 0 (1 - ((n + 1 : ℝ) / ρ) * max 0 (|(|x| - ρ)| - ρ / (n + 1 : ℝ))) = 0) := by sorry
