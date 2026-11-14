-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_shifted_exponential_nested_positive_changes_le_harmonic
-- name    : StabilityDichotomies.Bijunctive.shifted_exponential_nested_positive_changes_le_harmonic
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:05:01.396277+00:00
-- url     : https://prove2.me/theorems/cc465b09-ea5a-4f89-bd2a-c88710757396
-- title:
--   Nested positive shifted-exponential winner changes have harmonic probability sum
-- statement:
--   For independent rate-$\beta>0$ exponentials with fixed nonnegative offsets, let fixed candidate sets decrease in groups. Sum the probabilities that both before and after maxima are positive, the before maximum is unique, and their fixed labels differ. The sum is at most $H_{|S_0|}$. This averages over all positive-score patterns, including patterns of zero probability.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9, feasibility-root sensitivity step, equation (8).

import Mathlib
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter Function

theorem StabilityDichotomies.Bijunctive.shifted_exponential_nested_positive_changes_le_harmonic
    {α κ : Type} [Fintype α] (sets : ℕ → Finset α) (k : ℕ)
    (hsub : ∀ i < k, sets (i+1) ⊆ sets i) (label : α → κ)
    (d : α → ℝ) (hd : ∀ a, 0 ≤ d a) (β : ℝ) (hβ : 0 < β) :
    (∑ i ∈ Finset.range k,
      (Measure.pi (fun _ : α => expMeasure β)
        {x : α → ℝ | ∃ a ∈ sets i, ∃ b ∈ sets (i+1),
          0 < x a - d a ∧ 0 < x b - d b ∧
          (∀ j ∈ sets i, j ≠ a → x j - d j < x a - d a) ∧
          (∀ j ∈ sets (i+1), x j - d j ≤ x b - d b) ∧ label a ≠ label b}).toReal) ≤
      (harmonic (sets 0).card : ℝ) := by
  sorry
