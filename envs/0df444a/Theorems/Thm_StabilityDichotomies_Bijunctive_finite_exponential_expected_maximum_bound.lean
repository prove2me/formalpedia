-- Prove2me | Theorems.Thm_StabilityDichotomies_Bijunctive_finite_exponential_expected_maximum_bound
-- name    : StabilityDichotomies.Bijunctive.finite_exponential_expected_maximum_bound
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:16:02.561216+00:00
-- url     : https://prove2.me/theorems/b1f16a82-aab9-4bf2-9cc0-23102c769a68
-- title:
--   Expected maximum of finitely many exponential shifts
-- statement:
--   For a nonempty finite index set $A$ and independent rate-$\beta>0$ exponential shifts, the maximum with zero is integrable and has expectation at most $(\log |A|+1)/\beta$. This provides the logarithmic expected shift bound needed by the graph-deletion sensitivity analysis.
-- source:
--   Wang and Yoshida, Stability Dichotomies for Boolean CSPs, STOC 2027, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/535.pdf, proof of Theorem 4.9, graph-deletion sensitivity step.

import Mathlib
open scoped Classical ENNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter

theorem StabilityDichotomies.Bijunctive.finite_exponential_expected_maximum_bound {α : Type} [Fintype α] [Nonempty α]
    (β : ℝ) (hβ : 0 < β) :
    let μ := Measure.pi (fun _ : α => expMeasure β)
    let M := fun δ : α → ℝ => max 0 (Finset.univ.sup' Finset.univ_nonempty δ)
    Integrable M μ ∧ (∫ δ, M δ ∂μ) ≤ (Real.log (Fintype.card α) + 1) / β := by
  sorry
