-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_finite_shifted_exponential_scores_pairwise_distinct_ae
-- name    : StabilityDichotomies.Bijunctive.finite_shifted_exponential_scores_pairwise_distinct_ae
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:05:47.868507+00:00
-- url     : https://prove2.me/theorems/1c8db9c8-9bc2-474e-8e97-0fb818ae737b
-- title:
--   Finite shifted exponential scores are pairwise distinct almost surely
-- statement:
--   For a finite family of independent positive-rate exponential variables and arbitrary fixed real offsets, all shifted values are pairwise distinct almost surely.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9, feasibility-root sensitivity step.

import Mathlib
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter Function

theorem StabilityDichotomies.Bijunctive.finite_shifted_exponential_scores_pairwise_distinct_ae {α : Type} [Fintype α]
    (β : ℝ) (hβ : 0 < β) (d : α → ℝ) :
    ∀ᵐ x ∂(Measure.pi (fun _ : α => expMeasure β)),
      ∀ a b, a ≠ b → x a - d a ≠ x b - d b := by
  sorry
