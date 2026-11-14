-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_conditional_exponential_excess_expected_records
-- name    : StabilityDichotomies.Bijunctive.conditional_exponential_excess_expected_records
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:48:25.989559+00:00
-- url     : https://prove2.me/theorems/063cd7b9-0dc5-46e1-810f-ef40009ef98a
-- title:
--   Conditional positive shifted-exponential records have harmonic expectation
-- statement:
--   Condition a finite independent exponential family on a positive-probability coordinatewise event, requiring each selected coordinate to exceed its nonnegative threshold. In any fixed ordering of the selected coordinates, the number of strict suffix records among their shifted excesses is integrable and has conditional expectation exactly $H_{|S|}$. Other coordinates may satisfy arbitrary positive-probability measurable conditions.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9, feasibility-root sensitivity step, equation (8).

import Mathlib
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter Function

theorem StabilityDichotomies.Bijunctive.conditional_exponential_excess_expected_records
    {α : Type} [Fintype α] (S : Finset α) (ord : Fin S.card ≃ ↥S)
    (β : ℝ) (hβ : 0 < β) (d : α → ℝ) (s : α → Set ℝ)
    (hs : ∀ i, MeasurableSet (s i)) (hpos : ∀ i, (expMeasure β) (s i) ≠ 0)
    (hd : ∀ i ∈ S, 0 ≤ d i) (hselected : ∀ i ∈ S, s i = Ioi (d i)) :
    let μ := ProbabilityTheory.cond (Measure.pi (fun _ : α => expMeasure β)) (Set.univ.pi s)
    let R := fun x : α → ℝ => ∑ i : Fin S.card,
      if ∀ j ∈ Finset.Ici i, j ≠ i → x (ord j) - d (ord j) < x (ord i) - d (ord i)
      then (1 : ℝ) else 0
    Integrable R μ ∧ (∫ x, R x ∂μ) = (harmonic S.card : ℝ) := by
  sorry
