-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_conditional_exponential_nested_group_changes_le_harmonic
-- name    : StabilityDichotomies.Bijunctive.conditional_exponential_nested_group_changes_le_harmonic
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:56:41.588686+00:00
-- url     : https://prove2.me/theorems/6537da49-bf18-4417-84c0-d6f5a6a93a2e
-- title:
--   Conditional grouped winner changes have harmonic total probability
-- statement:
--   Condition independent exponentials on any positive-probability coordinatewise event in which each selected coordinate exceeds its nonnegative threshold. On any fixed decreasing sequence of subsets of selected coordinates, sum the conditional probabilities that the unique shifted-score maximum before a group removal and a maximum afterward have different fixed labels. This sum is at most the harmonic number of the initial candidate count.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9, feasibility-root sensitivity step, equation (8).

import Mathlib
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter

theorem StabilityDichotomies.Bijunctive.conditional_exponential_nested_group_changes_le_harmonic
    {α κ : Type} [Fintype α] (S : Finset α) (β : ℝ) (hβ : 0 < β)
    (d : α → ℝ) (s : α → Set ℝ)
    (hs : ∀ i, MeasurableSet (s i)) (hpos : ∀ i, (expMeasure β) (s i) ≠ 0)
    (hd : ∀ i ∈ S, 0 ≤ d i) (hselected : ∀ i ∈ S, s i = Ioi (d i))
    (sets : ℕ → Finset ↥S) (k : ℕ) (hsub : ∀ i < k, sets (i+1) ⊆ sets i)
    (label : ↥S → κ) :
    let μ := ProbabilityTheory.cond (Measure.pi (fun _ : α => expMeasure β)) (Set.univ.pi s)
    (∑ i ∈ Finset.range k, (μ
      {x : α → ℝ | ∃ a ∈ sets i, ∃ b ∈ sets (i+1),
        (∀ j ∈ sets i, j ≠ a → x j - d j < x a - d a) ∧
        (∀ j ∈ sets (i+1), x j - d j ≤ x b - d b) ∧ label a ≠ label b}).toReal) ≤
      (harmonic (sets 0).card : ℝ) := by
  sorry
