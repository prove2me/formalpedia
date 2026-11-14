-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_iid_exponential_group_removal_change_bound
-- name    : StabilityDichotomies.Bijunctive.iid_exponential_group_removal_change_bound
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:50:34.497122+00:00
-- url     : https://prove2.me/theorems/a44ed6b1-50a8-4711-aa4f-49d7ff976688
-- title:
--   Removing a candidate group changes the winner label with probability at most its fraction
-- statement:
--   For i.i.d. rate-$\beta>0$ exponential scores on a finite candidate set $T$, remove a subset $T\setminus S$ and compare arbitrary fixed labels of the original unique maximum and a maximum remaining in $S$. The probability that their labels differ is at most $|T\setminus S|/|T|$. The event explicitly requires the original maximum to be unique.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9, feasibility-root record analysis.

import Mathlib
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter

theorem StabilityDichotomies.Bijunctive.iid_exponential_group_removal_change_bound {α κ : Type} [Fintype α]
    (T S : Finset α) (hsub : S ⊆ T) (label : α → κ) (β : ℝ) (hβ : 0 < β) :
    (Measure.pi (fun _ : α => expMeasure β)
      {δ : α → ℝ | ∃ a ∈ T, ∃ b ∈ S,
        (∀ j ∈ T, j ≠ a → δ j < δ a) ∧
        (∀ j ∈ S, δ j ≤ δ b) ∧ label a ≠ label b}).toReal ≤
      ((T \ S).card : ℝ) / T.card := by
  sorry
