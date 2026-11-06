-- Prove2me | Theorems.Thm_ReserveLB_eq_3
-- name    : ReserveLB.eq_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:29:48.114591+00:00
-- url     : https://prove2.me/theorems/df0c2ccd-a44a-4390-9036-e8d64a9dae79
-- title:
--   Equation (3) — lower tail of a sum of independent $[0,1]$ variables
-- statement:
--   Let $Z_1, \dots, Z_n$ be independent random variables with values in $[0,1]$, $\mu = \mathbb E\sum_j Z_j$, and $0 < t \le \mu$. Then
--   $$
--   \mathbb P\Bigl[\sum_j Z_j \le t\Bigr] \le \exp\bigl(t\ln(\mu/t) + t - \mu\bigr).
--   $$
--
--   This lower-tail estimate pays the mean rows of (4) in the necessity argument of Lemma 3.1.
--
--   Differences from the source:
--   - encoding: Z_j ∈ [0, 1] independent → measurable Z_j, iIndepFun, 0 ≤ Z_j ω ≤ 1 for every ω; reason: as for (2); same instances
-- source:
--   Mahboub–Rahgoshay, Stochastic Load Balancing with Strict Machine-Reservation Budgets, manuscript of Oct. 30, 2026 (sha256 aefe1158e8000194527b025b3c358dcb571c94e1038c0bfdd295c6119bc9f630), Section 2.2, (3), p.4

import Mathlib

open MeasureTheory ProbabilityTheory

namespace ReserveLB

/-- **Equation (3) — lower tail of a sum of bounded independent variables.**
Mahboub–Rahgoshay, *Stochastic Load Balancing with Strict Machine-Reservation Budgets*,
manuscript of Oct. 30, 2026 (sha256 aefe1158…), Section 2.2, (3), p.4: "P[Σ_j Zj ≤ t] ≤ exp(t ln(µ/t) + t − µ), Zj ∈ [0, 1] independent,
µ = E Σ_j Zj ≥ t > 0."

Let `Z_1, …, Z_n` be independent random variables with values in `[0, 1]`, `µ = E Σ_j Z_j`, and
`0 < t ≤ µ`. Then `P[Σ_j Z_j ≤ t] ≤ exp(t ln(µ/t) + t − µ)`.

**Formalization Note.** Measurable variables on a probability space; independence is
`iIndepFun`. -/
theorem eq_3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (Z : Fin n → Ω → ℝ) (hZm : ∀ j, Measurable (Z j)) (hind : iIndepFun Z P)
    (hZ01 : ∀ j ω, 0 ≤ Z j ω ∧ Z j ω ≤ 1) (t : ℝ) (ht : 0 < t)
    (htμ : t ≤ ∫ ω, ∑ j, Z j ω ∂P) :
    P.real {ω | ∑ j, Z j ω ≤ t} ≤
      Real.exp (t * Real.log ((∫ ω, ∑ j, Z j ω ∂P) / t) + t - ∫ ω, ∑ j, Z j ω ∂P) := by sorry

end ReserveLB
