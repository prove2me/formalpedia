-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_uniform_label_independent_event_probability
-- name    : StabilityDichotomies.Bijunctive.uniform_label_independent_event_probability
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T11:12:05.664729+00:00
-- url     : https://prove2.me/theorems/82e4476a-2107-4186-83a6-0bdbacc8b582
-- title:
--   A uniform finite label transfers independent event probabilities to a finite average
-- statement:
--   Let $L$ be a uniformly distributed finite label and let $X$ be independent of $L$. Given a measurable event $E_l$ for each label $l$,
--   $$\Pr[X\in E_L]=\frac1{|\mathcal L|}\sum_{l\in\mathcal L}\Pr[X\in E_l].$$
--   This transfers conditional uniform cutoff-order events and independent exponential shifts to the finite combinatorial bounds in the proof of Theorem 4.9.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9, conditional ordering and independent shifts.

import Mathlib
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Function

theorem StabilityDichotomies.Bijunctive.uniform_label_independent_event_probability {Ω Δ ι : Type}
    [MeasurableSpace Ω] [MeasurableSpace Δ] [Fintype ι]
    (μ : Measure Ω) (ν : Measure Δ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (label : Ω → ι) (hlabel : ∀ i, MeasurableSet {ω | label ω = i})
    (huniform : ∀ i, μ.real {ω | label ω = i} = 1 / Fintype.card ι)
    (E : ι → Set Δ) (hE : ∀ i, MeasurableSet (E i)) :
    ((μ.prod ν) {z : Ω × Δ | z.2 ∈ E (label z.1)}).toReal =
      (1 / (Fintype.card ι : ℝ)) * ∑ i : ι, ν.real (E i) := by
  sorry
