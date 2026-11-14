-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_finite_independent_product_restriction
-- name    : StabilityDichotomies.Bijunctive.finite_independent_product_restriction
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:36:33.342516+00:00
-- url     : https://prove2.me/theorems/4c1c7cd2-7f20-4296-b195-ed0b0e1052e2
-- title:
--   Restriction of a finite product probability measure
-- statement:
--   For independent random variables indexed by a finite set, restriction to a subset is measure-preserving from the full product probability law to the product law of the selected coordinates. This permits the independent exponential shifts in Theorem 4.9 to be restricted to exactly the roots reaching a given clause.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9, approximation paragraph.

import Mathlib
open scoped Classical
open MeasureTheory ProbabilityTheory Set

theorem StabilityDichotomies.Bijunctive.finite_independent_product_restriction {α : Type} [Fintype α]
    (s : Finset α) (μ : α → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] :
    MeasurePreserving (fun x : α → ℝ => fun i : ↥s => x i)
      (Measure.pi μ) (Measure.pi (fun i : ↥s => μ i)) := by
  sorry
