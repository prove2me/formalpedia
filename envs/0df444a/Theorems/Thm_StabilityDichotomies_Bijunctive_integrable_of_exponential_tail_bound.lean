-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_integrable_of_exponential_tail_bound
-- name    : StabilityDichotomies.Bijunctive.integrable_of_exponential_tail_bound
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:14:21.740199+00:00
-- url     : https://prove2.me/theorems/74b34ce0-e215-457f-8b02-51e76aaa1439
-- title:
--   An exponential upper tail implies integrability
-- statement:
--   If an almost-everywhere nonnegative measurable random variable on a probability space has tail bounded by $q e^{-\beta t}$ for all $t\ge0$, where $q\ge0$ and $\beta>0$, then it is integrable.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9, graph-deletion sensitivity step.

import Mathlib
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter

theorem StabilityDichotomies.Bijunctive.integrable_of_exponential_tail_bound {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (hf : AEMeasurable f μ) (hnonneg : ∀ᵐ ω ∂μ, 0 ≤ f ω)
    (q β : ℝ) (hq : 0 ≤ q) (hβ : 0 < β)
    (htail : ∀ t : ℝ, 0 ≤ t → μ.real {ω | t < f ω} ≤ q * Real.exp (-β*t)) :
    Integrable f μ := by
  sorry
