-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_iid_continuous_rank_uniform
-- name    : StabilityDichotomies.Bijunctive.iid_continuous_rank_uniform
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:18:26.817499+00:00
-- url     : https://prove2.me/theorems/6979e4b4-a963-4307-ae8b-a1387ff653e5
-- title:
--   A designated coordinate in an iid atomless sample has uniform rank
-- statement:
--   Let $X_1,\ldots,X_n$ be independent, identically distributed real random variables, and suppose distinct coordinates tie with probability zero. For every coordinate $i$ and every $k\in\{0,\ldots,n-1\}$,
--   $$\Pr[\#\{j:X_j<X_i\}=k]=1/n.$$
--   This supplies the uniform-cutoff-rank component of the random ordering argument in Theorem 4.9.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9, random cutoff-rank argument.

import Mathlib
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter Function

theorem StabilityDichotomies.Bijunctive.iid_continuous_rank_uniform (n : ℕ) (μ₀ : Measure ℝ) [IsProbabilityMeasure μ₀]
    (htie : ∀ a b : Fin n, a ≠ b →
      Measure.pi (fun _ : Fin n => μ₀) {x | x a = x b} = 0)
    (i k : Fin n) :
    (Measure.pi (fun _ : Fin n => μ₀) {x | (Finset.univ.filter (fun j : Fin n => x j < x i)).card = k.val}).toReal = 1 / n := by
  sorry
