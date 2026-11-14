-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_shifted_exponential_top_gap
-- name    : StabilityDichotomies.Bijunctive.shifted_exponential_top_gap
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T07:59:53.42865+00:00
-- url     : https://prove2.me/theorems/3ec21b3e-6c7c-45c7-8ace-e0601829e272
-- title:
--   Gap between the two largest independently shifted exponential values
-- statement:
--   Let q ≥ 2, β > 0, t ≥ 0, and let d₁,…,d_q be fixed real numbers. Independently sample rate-β exponential shifts δᵢ and set Zᵢ=δᵢ−dᵢ. The probability that the largest two values, counting distinct indices, differ by at most t is at most 1−exp(−βt), which is at most βt. The event quantifies distinct indices attaining the largest and second-largest values, so ties are included.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean Constraint Satisfaction Problems, STOC 2027 submission #535, Lemma 4.5, p. 18, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf

import Mathlib
noncomputable section
open scoped Classical BigOperators
open MeasureTheory ProbabilityTheory

theorem StabilityDichotomies.Bijunctive.shifted_exponential_top_gap (q : ℕ) (hq : 2 ≤ q) (β t : ℝ)
    (hβ : 0 < β) (ht : 0 ≤ t) (d : Fin q → ℝ) :
    ((Measure.pi (fun _ : Fin q => expMeasure β))
      {δ : Fin q → ℝ | ∃ i j : Fin q, i ≠ j ∧
        (∀ k, δ k - d k ≤ δ i - d i) ∧
        (∀ k, k ≠ i → δ k - d k ≤ δ j - d j) ∧
        (δ i - d i) - (δ j - d j) ≤ t}).toReal ≤ 1 - Real.exp (-β * t) ∧
      1 - Real.exp (-β * t) ≤ β * t := by
  sorry
