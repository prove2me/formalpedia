-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_iid_continuous_order_uniform
-- name    : StabilityDichotomies.Bijunctive.iid_continuous_order_uniform
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:20:30.468043+00:00
-- url     : https://prove2.me/theorems/2716b610-1154-4fe0-a25b-88e6c5b8dcbf
-- title:
--   The complete ordering of an iid atomless sample is uniform
-- statement:
--   For $n$ independent identically distributed real random variables with no pairwise ties, every strict ordering of the $n$ coordinates occurs with probability $1/n!$. This is the joint random priority and cutoff ordering used in the proof of Theorem 4.9.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9, random cutoff-rank argument.

import Mathlib
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter Function

theorem StabilityDichotomies.Bijunctive.iid_continuous_order_uniform (n : ℕ) (μ₀ : Measure ℝ) [IsProbabilityMeasure μ₀]
    (htie : ∀ a b : Fin n, a ≠ b →
      Measure.pi (fun _ : Fin n => μ₀) {x | x a = x b} = 0)
    (e : Equiv.Perm (Fin n)) :
    (Measure.pi (fun _ : Fin n => μ₀)
      {x | ∀ i, (Finset.univ.filter (fun j : Fin n => x j < x i)).card = (e i).val}).toReal = 1 / n.factorial := by
  sorry
