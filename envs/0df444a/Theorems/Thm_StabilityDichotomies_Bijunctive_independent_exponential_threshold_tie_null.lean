-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_independent_exponential_threshold_tie_null
-- name    : StabilityDichotomies.Bijunctive.independent_exponential_threshold_tie_null
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:25:02.190237+00:00
-- url     : https://prove2.me/theorems/2c09dd67-3c26-4597-92e0-33d3616dc8df
-- title:
--   An exponential variable almost surely differs from an independent threshold
-- statement:
--   An exponential random variable of positive rate equals any independent measurable real threshold on a product probability space with probability zero.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean Constraint Satisfaction Problems, STOC 2027 submission #535, Lemma 4.5, p. 18, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf

import Mathlib
noncomputable section
open scoped Classical BigOperators ENNReal
open MeasureTheory ProbabilityTheory Set

theorem StabilityDichotomies.Bijunctive.independent_exponential_threshold_tie_null {Ω : Type} [MeasurableSpace Ω]
    (ν : Measure Ω) [SFinite ν] (a : Ω → ℝ) (ha : Measurable a)
    (β : ℝ) (hβ : 0 < β) :
    (expMeasure β).prod ν {z : ℝ × Ω | z.1 = a z.2} = 0 := by sorry
