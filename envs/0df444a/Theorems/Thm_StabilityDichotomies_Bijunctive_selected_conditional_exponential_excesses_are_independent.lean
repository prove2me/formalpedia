-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_selected_conditional_exponential_excesses_are_independent
-- name    : StabilityDichotomies.Bijunctive.selected_conditional_exponential_excesses_are_independent
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:38:17.305405+00:00
-- url     : https://prove2.me/theorems/f911b66e-8fc7-4653-9e1b-9cf24de78ab8
-- title:
--   Selected positive shifted exponentials remain independent exponentials
-- statement:
--   For a finite independent rate-$\beta>0$ exponential family, condition on a positive-probability measurable rectangle. On each selected coordinate the condition is that the shift exceeds a nonnegative threshold. After restricting to those selected coordinates and subtracting their thresholds, the resulting joint law is exactly the product of independent rate-$\beta$ exponential laws. The remaining coordinates may satisfy arbitrary positive-probability measurable conditions.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9, feasibility-root sensitivity step.

import Mathlib
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter

theorem StabilityDichotomies.Bijunctive.selected_conditional_exponential_excesses_are_independent
    {α : Type} [Fintype α] (S : Finset α) (β : ℝ) (hβ : 0 < β)
    (d : α → ℝ) (s : α → Set ℝ)
    (hs : ∀ i, MeasurableSet (s i)) (hpos : ∀ i, (expMeasure β) (s i) ≠ 0)
    (hd : ∀ i ∈ S, 0 ≤ d i) (hselected : ∀ i ∈ S, s i = Ioi (d i)) :
    (ProbabilityTheory.cond (Measure.pi (fun _ : α => expMeasure β)) (Set.univ.pi s)).map
      (fun x : α → ℝ => fun i : ↥S => x i - d i) =
      Measure.pi (fun _ : ↥S => expMeasure β) := by
  sorry
