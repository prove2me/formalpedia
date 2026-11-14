-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_iid_exponential_unique_maximum_uniform
-- name    : StabilityDichotomies.Bijunctive.iid_exponential_unique_maximum_uniform
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:40:55.514808+00:00
-- url     : https://prove2.me/theorems/754105a8-c9d5-4f61-a4e7-142608708012
-- title:
--   Each i.i.d. exponential coordinate is uniquely maximal with probability 1/n
-- statement:
--   For $n\ge1$ independent identically distributed rate-$\beta>0$ exponential variables, any specified coordinate is the unique maximum with probability $1/n$. This is the basic record-probability estimate in the feasibility-root sensitivity analysis.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9, feasibility-root sensitivity step.

import Mathlib
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter Function

theorem StabilityDichotomies.Bijunctive.iid_exponential_unique_maximum_uniform (n : ℕ) (β : ℝ) (hβ : 0 < β) (i : Fin n) :
    (Measure.pi (fun _ : Fin n => expMeasure β)
      {δ : Fin n → ℝ | ∀ j, j ≠ i → δ j < δ i}).toReal = 1 / n := by
  sorry
