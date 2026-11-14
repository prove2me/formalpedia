-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_finite_exponential_maximum_tail_bound
-- name    : StabilityDichotomies.Bijunctive.finite_exponential_maximum_tail_bound
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:08:28.36343+00:00
-- url     : https://prove2.me/theorems/47ced059-6d0e-4913-92c8-6ab0fd68fa4c
-- title:
--   Tail bound for the maximum of finitely many exponential shifts
-- statement:
--   For a finite family of independent rate-$\beta>0$ exponential variables, the probability that at least one exceeds $t\ge0$ is at most $|A|e^{-\beta t}$. This is a tail estimate toward bounding the expected maximum in the graph-deletion sensitivity analysis.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9, graph-deletion sensitivity step.

import Mathlib
open scoped Classical BigOperators ENNReal
open MeasureTheory ProbabilityTheory Set

theorem StabilityDichotomies.Bijunctive.finite_exponential_maximum_tail_bound {α : Type} [Fintype α]
    (β t : ℝ) (hβ : 0 < β) (ht : 0 ≤ t) :
    ((Measure.pi (fun _ : α => expMeasure β)) {δ : α → ℝ | ∃ i, t < δ i}).toReal ≤
      (Fintype.card α : ℝ) * Real.exp (-β*t) := by
  sorry
