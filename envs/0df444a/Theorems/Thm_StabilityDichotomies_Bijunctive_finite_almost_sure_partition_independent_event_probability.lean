-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_finite_almost_sure_partition_independent_event_probability
-- name    : StabilityDichotomies.Bijunctive.finite_almost_sure_partition_independent_event_probability
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T11:13:21.007434+00:00
-- url     : https://prove2.me/theorems/d9818882-07dc-4633-9434-13edbb1e789e
-- title:
--   Finite almost-sure partition transfers independent event probabilities
-- statement:
--   Partition the first factor of an independent product probability space into finitely many measurable events, up to a null set. If an event in the product is described on each partition cell by a measurable event in the second factor, its probability equals the sum of the cell probability times the corresponding second-factor event probability. This transfers conditional priority orderings to independent exponential-shift event costs.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9, conditional ordering and independent shifts.

import Mathlib
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Function

theorem StabilityDichotomies.Bijunctive.finite_almost_sure_partition_independent_event_probability {Ω Δ ι : Type}
    [MeasurableSpace Ω] [MeasurableSpace Δ] [Fintype ι]
    (μ : Measure Ω) (ν : Measure Δ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (P : ι → Set Ω) (hP : ∀ i, MeasurableSet (P i)) (hdis : Pairwise (Disjoint on P))
    (hcover : ∀ᵐ ω ∂μ, ∃ i, ω ∈ P i)
    (E : ι → Set Δ) (hE : ∀ i, MeasurableSet (E i)) (T : Set (Ω × Δ))
    (hsection : ∀ i ω δ, ω ∈ P i → ((ω,δ) ∈ T ↔ δ ∈ E i)) :
    ((μ.prod ν) T).toReal = ∑ i : ι, μ.real (P i) * ν.real (E i) := by
  sorry
