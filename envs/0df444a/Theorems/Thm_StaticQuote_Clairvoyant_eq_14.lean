-- Prove2me | Theorems.Thm_StaticQuote_Clairvoyant_eq_14
-- name    : StaticQuote.Clairvoyant.eq_14
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:16:07.931359+00:00
-- url     : https://prove2.me/theorems/28c679ec-c846-4d76-9a19-660cb68004bc
-- title:
--   (14), p. 18 — lim sup_M λ E[γ_{1:M}/M] ≤ C^π for every FCFS schedule
-- statement:
--   Under the standing assumptions of the model, let $y$ be any FCFS-feasible schedule and $C(y)$ its long-run average cost in the per-customer form (4). Then
--   $$\limsup_{M\to\infty}\ \lambda\,\mathbb E\Big[\frac{\gamma_{1:M}(\omega)}{M}\Big] \le C(y),$$
--   where $\lambda = 1/\mathbb E[T_1]$ is the arrival rate.
--
--   Taking expectations and $\limsup$ in the sample-path bound gives this asymptotic clairvoyant lower bound on the cost of every policy. It is equation (14), the first half of the proof of Theorem 4.
--
--   **Formalization Note.** The paper states (14) for every policy of its class $\Pi$; it is stated here for every FCFS-feasible schedule, a class containing $\Pi$. Expectations and the $\limsup$ are taken in $[0,\infty]$.
-- source:
--   Farahani, Dawande, Janakiraman, Order Now, Pickup in 30 Minutes, SSRN 3557605 (version of 2021-08-05), p. 18, (14)

import Mathlib
import Definitions.Def_StaticQuote_Clairvoyant_Setting

open MeasureTheory Filter
open scoped ENNReal

namespace StaticQuote.Clairvoyant

/-- Farahani, Dawande, Janakiraman, Order Now, Pickup in 30 Minutes, SSRN 3557605 (version of 2021-08-05), p. 18, (14): `lim sup_{M→∞} λ E[γ_{1:M}(ω)/M] ≤ C^π` for every policy π, here for every
FCFS-feasible schedule `y`.

**Formalization Notes.** `C^π` is `Model.cost`, the per-customer form (4); expectations are
`lintegral`s and the lim sup is taken in `ℝ≥0∞`. λ stays inside the lim sup as printed. The
quantification over all FCFS-feasible schedules widens the paper's class Π (which it contains). -/
theorem eq_14 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} (Q : Model Ω) (hQ : Q.Standing μ)
    (y : ℕ → Ω → ℝ) (hy : Q.IsFCFSSchedule y) :
    limsup (fun M : ℕ => ENNReal.ofReal (Q.rate μ) * ∫⁻ ω, Q.gamma 1 M ω / (M : ℝ≥0∞) ∂μ) atTop
      ≤ Q.cost μ y := by sorry

end StaticQuote.Clairvoyant
