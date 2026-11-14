-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_exponential_interval_hazard_bound
-- name    : StabilityDichotomies.Bijunctive.exponential_interval_hazard_bound
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:15:47.717733+00:00
-- url     : https://prove2.me/theorems/e4828209-72b9-4516-aa6e-c07b5065ba63
-- title:
--   Exponential short-interval hazard bound
-- statement:
--   For X distributed exponentially with rate β > 0, any real threshold a and t ≥ 0, P(a < X ≤ a+t) is at most (1−exp(−βt))P(X>a), and this is at most βt·P(X>a). The bound remains valid for thresholds below zero and provides the conditional one-coordinate estimate for the shifted-exponential gap lemma.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean Constraint Satisfaction Problems, STOC 2027 submission #535, Lemma 4.5, p. 18, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf

import Mathlib
noncomputable section
open MeasureTheory ProbabilityTheory Set

theorem StabilityDichotomies.Bijunctive.exponential_interval_hazard_bound (β a t : ℝ) (hβ : 0 < β) (ht : 0 ≤ t) :
    (expMeasure β).real (Ioc a (a+t)) ≤
      (1 - Real.exp (-β * t)) * (expMeasure β).real (Ioi a) ∧
    (1 - Real.exp (-β * t)) * (expMeasure β).real (Ioi a) ≤
      (β * t) * (expMeasure β).real (Ioi a) := by sorry
