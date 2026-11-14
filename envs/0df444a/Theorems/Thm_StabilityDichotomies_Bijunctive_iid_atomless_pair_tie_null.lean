-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_iid_atomless_pair_tie_null
-- name    : StabilityDichotomies.Bijunctive.iid_atomless_pair_tie_null
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:21:34.081026+00:00
-- url     : https://prove2.me/theorems/2d528a5e-7926-4d00-bc5a-625816e4caf8
-- title:
--   Independent atomless coordinates have zero tie probability
-- statement:
--   Two distinct coordinates of a finite independent sample from an atomless probability measure coincide with probability zero. This verifies the no-ties hypothesis needed for the random cutoff ordering in Theorem 4.9.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9, random cutoff-rank argument.

import Mathlib
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter Function

theorem StabilityDichotomies.Bijunctive.iid_atomless_pair_tie_null (n : ℕ) (μ₀ : Measure ℝ) [IsProbabilityMeasure μ₀]
    [NullSingletonClass μ₀] (i j : Fin n) (hij : i ≠ j) :
    Measure.pi (fun _ : Fin n => μ₀) {x | x i = x j} = 0 := by
  sorry
