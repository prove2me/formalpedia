-- Prove2me | Theorems.Thm_ReserveLB_lemma_2_4
-- name    : ReserveLB.lemma_2_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:30:20.624417+00:00
-- url     : https://prove2.me/theorems/cdb55789-da54-441d-a504-31fe1bec9cdc
-- title:
--   Lemma 2.4 — global large-tail payment $\sum_j \mathbb E[Q_j\mathbf 1\{Q_j\ge T\}] \le -T\ln(1-J/T)$
-- statement:
--   Let $Q_1, \dots, Q_n$ be independent nonnegative random variables with
--   $$
--   J = \mathbb E\max_j Q_j < T .
--   $$
--   Then
--   $$
--   \sum_j \mathbb E\bigl[Q_j\,\mathbf 1\{Q_j \ge T\}\bigr] \le -T\ln\Bigl(1 - \frac JT\Bigr).
--   $$
--
--   With $Q_j$ the size of job $j$ on its fastest reserved endpoint, this pays the full-exception row of (4).
--
--   Differences from the source:
--   - encoding: J = E max_j Q_j < T → the lower Lebesgue integral of max_j Q_j is < T, and J is its real value; reason: this also asserts that E max_j Q_j is finite, so a non-integrable maximum cannot pass as J = 0; same instances
--   - encoding: independent nonnegative Q_j → measurable Q_j, iIndepFun, Q_j ω ≥ 0 for every ω; reason: as for (2); same instances
-- source:
--   Mahboub–Rahgoshay, Stochastic Load Balancing with Strict Machine-Reservation Budgets, manuscript of Oct. 30, 2026 (sha256 aefe1158e8000194527b025b3c358dcb571c94e1038c0bfdd295c6119bc9f630), Lemma 2.4, p.4

import Mathlib

open MeasureTheory ProbabilityTheory

namespace ReserveLB

/-- **Lemma 2.4 — global large-tail payment.**
Mahboub–Rahgoshay, *Stochastic Load Balancing with Strict Machine-Reservation Budgets*,
manuscript of Oct. 30, 2026 (sha256 aefe1158…), Lemma 2.4, p.4: "For independent nonnegative Qj, J = E maxj Qj < T,
Σ_j E[Qj 1{Qj≥T}] ≤ −T ln(1 − J/T)."

Let `Q_1, …, Q_n` be independent nonnegative random variables, and suppose
`J = E max_j Q_j < T`. Then `Σ_j E[Q_j 1{Q_j ≥ T}] ≤ −T ln(1 − J/T)`.

**Formalization Note.** `E max_j Q_j` is the lower Lebesgue integral of the nonnegative maximum, so
the hypothesis `J < T` also asserts that it is finite (a non-integrable maximum cannot pass as
`J = 0`); `J` is its real value. The maximum over no jobs is `0`. -/
theorem lemma_2_4 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (Q : Fin n → Ω → ℝ) (hQm : ∀ j, Measurable (Q j)) (hind : iIndepFun Q P)
    (hQ0 : ∀ j ω, 0 ≤ Q j ω) (T : ℝ)
    (hJ : ∫⁻ ω, ENNReal.ofReal (⨆ j, Q j ω) ∂P < ENNReal.ofReal T) :
    ∑ j, ∫ ω, Set.indicator {ω | T ≤ Q j ω} (Q j) ω ∂P ≤
      -T * Real.log (1 - (∫⁻ ω, ENNReal.ofReal (⨆ j, Q j ω) ∂P).toReal / T) := by sorry

end ReserveLB
