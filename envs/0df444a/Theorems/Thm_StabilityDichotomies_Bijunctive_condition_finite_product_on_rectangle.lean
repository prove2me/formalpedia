-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_condition_finite_product_on_rectangle
-- name    : StabilityDichotomies.Bijunctive.condition_finite_product_on_rectangle
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:37:06.210958+00:00
-- url     : https://prove2.me/theorems/626b15c0-3205-4602-9c4f-f3a368f5c7d4
-- title:
--   Conditioning a finite independent product on a positive rectangle
-- statement:
--   For a finite family of independent probability measures, conditioning their product on a measurable rectangle whose coordinate events all have positive probability gives the product of the individual conditional measures. This preserves independence under coordinatewise threshold conditions.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9, feasibility-root sensitivity step.

import Mathlib
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter

theorem StabilityDichotomies.Bijunctive.condition_finite_product_on_rectangle {α : Type} [Fintype α]
    (μ : α → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] (s : α → Set ℝ)
    (hs : ∀ i, MeasurableSet (s i)) (hpos : ∀ i, μ i (s i) ≠ 0) :
    ProbabilityTheory.cond (Measure.pi μ) (Set.univ.pi s) =
      Measure.pi (fun i => ProbabilityTheory.cond (μ i) (s i)) := by
  sorry
