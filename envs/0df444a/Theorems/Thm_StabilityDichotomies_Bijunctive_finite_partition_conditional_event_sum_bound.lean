-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_finite_partition_conditional_event_sum_bound
-- name    : StabilityDichotomies.Bijunctive.finite_partition_conditional_event_sum_bound
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:02:05.536279+00:00
-- url     : https://prove2.me/theorems/c8150525-e00f-4dba-a5aa-8bd6d6bd040d
-- title:
--   A uniform conditional event-sum bound survives finite averaging
-- statement:
--   For a finite measurable partition of a probability space and finitely many measurable events, if the sum of their conditional probabilities is at most $B$ on every positive-probability partition cell, then the unconditional sum is at most $B$. Zero-probability cells need no conditional estimate.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9, averaging over positive-score patterns.

import Mathlib
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter Function

theorem StabilityDichotomies.Bijunctive.finite_partition_conditional_event_sum_bound
    {Ω ι τ : Type} [MeasurableSpace Ω] [Fintype ι] [Fintype τ]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (P : ι → Set Ω) (E : τ → Set Ω) (B : ℝ)
    (hP : ∀ i, MeasurableSet (P i)) (hE : ∀ j, MeasurableSet (E j))
    (hdis : Pairwise (Disjoint on P)) (hcover : (⋃ i, P i) = Set.univ)
    (hB : 0 ≤ B)
    (hcond : ∀ i, μ (P i) ≠ 0 → ∑ j, (ProbabilityTheory.cond μ (P i)).real (E j) ≤ B) :
    (∑ j, μ.real (E j)) ≤ B := by
  sorry
