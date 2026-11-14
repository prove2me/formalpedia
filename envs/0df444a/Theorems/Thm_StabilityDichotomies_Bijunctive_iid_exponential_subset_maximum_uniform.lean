-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_iid_exponential_subset_maximum_uniform
-- name    : StabilityDichotomies.Bijunctive.iid_exponential_subset_maximum_uniform
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:42:01.623597+00:00
-- url     : https://prove2.me/theorems/b811719e-ed3d-417d-8ba9-51dbf97a2e47
-- title:
--   A specified index is maximal on a subset with probability 1/|S|
-- statement:
--   For independent rate-$\beta>0$ exponential values indexed by a finite set, and any nonempty subset $S$ containing $i$, the probability that $i$ is the unique maximum over $S$ is exactly $1/|S|$. Coordinates outside $S$ are unrestricted.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9, feasibility-root record analysis.

import Mathlib
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter Function

theorem StabilityDichotomies.Bijunctive.iid_exponential_subset_maximum_uniform {α : Type} [Fintype α]
    (S : Finset α) (i : α) (hi : i ∈ S) (β : ℝ) (hβ : 0 < β) :
    (Measure.pi (fun _ : α => expMeasure β)
      {δ : α → ℝ | ∀ j ∈ S, j ≠ i → δ j < δ i}).toReal = 1 / S.card := by
  sorry
