-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_product_probability_le_ae_fiber_bound
-- name    : StabilityDichotomies.Bijunctive.product_probability_le_ae_fiber_bound
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:48:08.988482+00:00
-- url     : https://prove2.me/theorems/e702040f-5a40-49dd-9b62-46fb9173c490
-- title:
--   A uniform almost-everywhere fiber bound controls product measure
-- statement:
--   If the first factor is a probability measure, the second is s-finite, and almost every first-coordinate fiber of a measurable event has second-factor measure at most $c$, then the event has product measure at most $c$. This integrates the fixed-subinstance clause bound over independent priority and cutoff randomness.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9, approximation paragraph.

import Mathlib
open scoped Classical ENNReal
open MeasureTheory Set Filter

theorem StabilityDichotomies.Bijunctive.product_probability_le_ae_fiber_bound {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [SFinite ν]
    (E : Set (α × β)) (hE : MeasurableSet E) (c : ℝ≥0∞)
    (hbound : ∀ᵐ x ∂μ, ν {y | (x,y) ∈ E} ≤ c) :
    (μ.prod ν) E ≤ c := by
  sorry
