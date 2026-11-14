-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_iid_exponential_expected_suffix_records
-- name    : StabilityDichotomies.Bijunctive.iid_exponential_expected_suffix_records
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:45:07.672599+00:00
-- url     : https://prove2.me/theorems/82c229dc-5539-470f-9dda-92b9b833ac2a
-- title:
--   Expected suffix-record count of i.i.d. exponential values is harmonic
-- statement:
--   For $n$ independent rate-$\beta>0$ exponential values in a fixed order, the number of indices whose value is strictly larger than every later value is integrable and has expectation exactly $H_n=\sum_{k=1}^n 1/k$. This is the source’s harmonic record estimate for roots removed in a shift-independent order.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9, feasibility-root sensitivity step, equation (8).

import Mathlib
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter

theorem StabilityDichotomies.Bijunctive.iid_exponential_expected_suffix_records (n : ℕ) (β : ℝ) (hβ : 0 < β) :
    let μ := Measure.pi (fun _ : Fin n => expMeasure β)
    let R := fun δ : Fin n → ℝ => ∑ i : Fin n,
      if ∀ j ∈ Finset.Ici i, j ≠ i → δ j < δ i then (1 : ℝ) else 0
    Integrable R μ ∧ (∫ δ, R δ ∂μ) = (harmonic n : ℝ) := by
  sorry
