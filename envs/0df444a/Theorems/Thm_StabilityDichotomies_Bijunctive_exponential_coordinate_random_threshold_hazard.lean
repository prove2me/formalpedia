-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_exponential_coordinate_random_threshold_hazard
-- name    : StabilityDichotomies.Bijunctive.exponential_coordinate_random_threshold_hazard
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:25:01.014197+00:00
-- url     : https://prove2.me/theorems/e8f7b8c1-d3c0-4bd5-a148-8d2606cd38f3
-- title:
--   Coordinatewise exponential hazard under a finite independent product
-- statement:
--   For independent rate-β exponential coordinates, take any coordinate i and any measurable threshold depending only on the other coordinates. The probability that coordinate i falls in the interval immediately above that threshold with width t is at most (1−exp(−βt)) times its probability of exceeding the threshold, for β > 0 and t ≥ 0.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean Constraint Satisfaction Problems, STOC 2027 submission #535, Lemma 4.5, p. 18, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf

import Mathlib
noncomputable section
open scoped Classical BigOperators ENNReal
open MeasureTheory ProbabilityTheory Set

theorem StabilityDichotomies.Bijunctive.exponential_coordinate_random_threshold_hazard (n : ℕ) (i : Fin (n+1))
    (a : (Fin n → ℝ) → ℝ) (ha : Measurable a) (β t : ℝ) (hβ : 0 < β) (ht : 0 ≤ t) :
    (Measure.pi (fun _ : Fin (n+1) => expMeasure β)
      {δ | a (i.removeNth δ) < δ i ∧ δ i ≤ a (i.removeNth δ) + t}) ≤
      ENNReal.ofReal (1 - Real.exp (-β*t)) *
        (Measure.pi (fun _ : Fin (n+1) => expMeasure β)
          {δ | a (i.removeNth δ) < δ i}) := by sorry
