-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_finite_index_shifted_exponential_top_gap
-- name    : StabilityDichotomies.Bijunctive.finite_index_shifted_exponential_top_gap
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:32:57.304198+00:00
-- url     : https://prove2.me/theorems/cfb852dd-b775-4ec4-9d3f-047c1472dcac
-- title:
--   Shifted-exponential top gap on an arbitrary finite index set
-- statement:
--   For a finite set of at least two indices, take independent rate-$\beta>0$ exponential random variables and subtract fixed real offsets. The probability that the largest and second-largest shifted values differ by at most $t\ge0$ is at most $1-e^{-\beta t}$. This arbitrary-index version of Lemma 4.5 allows direct use on the finite set of feasible roots reaching a clause.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, Lemma 4.5 and proof of Theorem 4.9.

import Theorems.Thm_StabilityDichotomies_Bijunctive_shifted_exponential_top_gap
open scoped Classical ENNReal
open MeasureTheory ProbabilityTheory Set

theorem StabilityDichotomies.Bijunctive.finite_index_shifted_exponential_top_gap {α : Type} [Fintype α] (hcard : 2 ≤ Fintype.card α)
    (β t : ℝ) (hβ : 0 < β) (ht : 0 ≤ t) (d : α → ℝ) :
    ((Measure.pi (fun _ : α => expMeasure β))
      {δ : α → ℝ | ∃ i j, i ≠ j ∧ (∀ k, δ k - d k ≤ δ i - d i) ∧
        (∀ k, k ≠ i → δ k - d k ≤ δ j - d j) ∧
        (δ i - d i) - (δ j - d j) ≤ t}).toReal ≤ 1 - Real.exp (-β*t) := by
  sorry
