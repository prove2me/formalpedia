-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_exponential_tail_shift_bound
-- name    : StabilityDichotomies.Bijunctive.exponential_tail_shift_bound
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:12:57.926236+00:00
-- url     : https://prove2.me/theorems/7fe41355-65df-41c4-b916-fcce8d140874
-- title:
--   Exponential tail shift bound for arbitrary thresholds
-- statement:
--   Let X be exponential with rate β > 0. For every real threshold a and t ≥ 0, the probability that X > a+t is at least exp(−βt) times the probability that X > a. This includes negative a, where the exponential distribution is supported on the nonnegative half-line, and is the memoryless tail inequality needed for the shifted-exponential top-gap argument.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean Constraint Satisfaction Problems, STOC 2027 submission #535, Lemma 4.5, p. 18, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf

import Mathlib
noncomputable section
open MeasureTheory ProbabilityTheory Set

theorem StabilityDichotomies.Bijunctive.exponential_tail_shift_bound (β a t : ℝ) (hβ : 0 < β) (ht : 0 ≤ t) :
    Real.exp (-β * t) * (expMeasure β).real (Ioi a) ≤ (expMeasure β).real (Ioi (a+t)) := by sorry
