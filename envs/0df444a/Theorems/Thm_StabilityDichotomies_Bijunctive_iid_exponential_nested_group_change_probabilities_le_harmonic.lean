-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_iid_exponential_nested_group_change_probabilities_le_harmonic
-- name    : StabilityDichotomies.Bijunctive.iid_exponential_nested_group_change_probabilities_le_harmonic
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:53:30.276288+00:00
-- url     : https://prove2.me/theorems/64bf2671-5f72-41f4-bf99-1de44b43c62b
-- title:
--   Nested candidate-set winner changes have harmonic total probability
-- statement:
--   Let $S_0\supseteq S_1\supseteq\cdots\supseteq S_k$ be any fixed nested finite candidate sets with fixed labels and independent identically distributed positive-rate exponential scores. Sum, over all steps, the probability that the unique maximum of $S_i$ and a maximum of $S_{i+1}$ have different labels. This sum is at most $H_{|S_0|}$.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9, feasibility-root sensitivity step, equation (8).

import Mathlib
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter

theorem StabilityDichotomies.Bijunctive.iid_exponential_nested_group_change_probabilities_le_harmonic
    {α κ : Type} [Fintype α] (sets : ℕ → Finset α) (k : ℕ)
    (hsub : ∀ i < k, sets (i+1) ⊆ sets i) (label : α → κ) (β : ℝ) (hβ : 0 < β) :
    (∑ i ∈ Finset.range k,
      (Measure.pi (fun _ : α => expMeasure β)
        {δ : α → ℝ | ∃ a ∈ sets i, ∃ b ∈ sets (i+1),
          (∀ j ∈ sets i, j ≠ a → δ j < δ a) ∧
          (∀ j ∈ sets (i+1), δ j ≤ δ b) ∧ label a ≠ label b}).toReal) ≤
      (harmonic (sets 0).card : ℝ) := by
  sorry
