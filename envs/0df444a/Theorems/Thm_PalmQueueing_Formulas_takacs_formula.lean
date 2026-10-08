-- Prove2me | Theorems.Thm_PalmQueueing_Formulas_takacs_formula
-- name    : PalmQueueing.Formulas.takacs_formula
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T01:14:11.931712+00:00
-- url     : https://prove2.me/theorems/bc399527-443c-4bdc-8e5c-5603e16c6dc0
-- title:
--   Eq. (3.4.44) — Takács' formula
-- statement:
--   **Takács' formula.** In a $GI/GI/1/\infty$ queue, where $\sigma_n$ is independent of
--   $W(T_n-)$,
--   $$ iu\,E[e^{iuW(0)}] = \lambda E^0_A[e^{iuW(0-)}]\big(E[e^{iu\sigma_0}] - 1\big) + iu(1-\rho) .
--   \tag{3.4.44} $$
--   The book's own attribution: "This formula is due to Takács."
--
--   It is the characteristic-function description of the stationary workload law, and §3.4's route to
--   it is the **rate conservation principle** of Chapter 1 applied to $Y(t) = e^{iuW(t)}$, which gives
--   $$ -iuE[e^{iuW(0)}] + iuP(X(0)=0) + \lambda E^0_A[e^{iuW(0)} - e^{iuW(0-)}] = 0 , $$
--   together with the factorisation the independence buys,
--   $$ E^0_A[e^{iuW(0)} - e^{iuW(0-)}] = E^0_A[e^{iuW(0-)}]\big(E^0_A[e^{iu\sigma_0}] - 1\big) ,
--   \tag{3.4.43} $$
--   and $P(X(0)=0) = 1-\rho$.
--
--   Note which expectation is which: $E^0_A[e^{iuW(0-)}]$ is a **Palm** expectation of the workload
--   **just before** an arrival, while $E[e^{iuW(0)}]$ and $E[e^{iu\sigma_0}]$ are stationary.
--   Confusing the two collapses the formula into a tautology.
--
--   Two hypotheses are what "$GI/GI/1/\infty$" means rather than steps of the proof: the service times
--   have the same law under $P^0_A$ as under $P$ (which the page states as
--   $E^0_A[e^{iu\sigma_0}] = E[e^{iu\sigma_0}]$), and $P(X(0)=0) = 1-\rho$. The workload is a
--   measurable, $\theta_t$-compatible solution of Lindley's equation with $\rho < 1$.
-- source:
--   Baccelli & Bremaud, Elements of Queueing Theory: Palm Martingale Calculus and Stochastic Recurrences, 2nd ed., Springer 2003, p. 232, Eq. (3.4.44)

import Mathlib
import Definitions.Def_PalmQueueing_Palm_PointProcess
import Definitions.Def_PalmQueueing_Loynes_SingleServerQueue

/-!
# Eq. (3.4.44): Takács' formula (§3.4, p.232)
-/

namespace PalmQueueing.Formulas

open MeasureTheory
open PalmQueueing.Palm PalmQueueing.Loynes

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Takács' formula**, Eq. (3.4.44) (p.232). In a `GI/GI/1/∞` queue, where `σ_n` is independent
of `W(T_n−)`,

`(3.4.44)  iu E[e^{iuW(0)}] = λ E⁰_A[e^{iuW(0−)}] (E[e^{iuσ_0}] − 1) + iu(1 − ρ)`.

The book's own attribution: "This formula is due to Takács."

It is the characteristic-function form of the stationary workload law, and the whole of §3.4's
route to it is the rate conservation principle of Chapter 1 applied to `Y(t) = e^{iuW(t)}`, which
gives

`−iu E[e^{iuW(0)}] + iu P(X(0) = 0) + λ E⁰_A[e^{iuW(0)} − e^{iuW(0−)}] = 0`,

together with the factorisation `(3.4.43)`
`E⁰_A[e^{iuW(0)} − e^{iuW(0−)}] = E⁰_A[e^{iuW(0−)}](E⁰_A[e^{iuσ_0}] − 1)` that the independence
buys, and `P(X(0) = 0) = 1 − ρ`.

Note which expectation is which: `E⁰_A[e^{iuW(0−)}]` is a **Palm** expectation of the workload
**just before** an arrival, while `E[e^{iuW(0)}]` and `E[e^{iuσ_0}]` are stationary. Confusing the
two collapses the formula into a tautology.

Two hypotheses are what "`GI/GI/1/∞`" means here rather than steps of the proof, and are carried
as such: the service times have the same law under `P⁰_A` as under `P` (the "GI" of the service
sequence, which the page states as `E⁰_A[e^{iuσ_0}] = E[e^{iuσ_0}]`), and `P(X(0) = 0) = 1 − ρ`. -/
theorem takacs_formula (Q : Queue Ω) (W Wl : ℝ → Ω → ℝ)
    (hW : IsWorkload Q W Wl) (hWmeas : ∀ t, Measurable (W t))
    (hWcomp : IsCompatible Q.toPalmSetting.θ W)
    (hstable : Q.rho < 1)
    (hindep : ∀ n : ℤ, ProbabilityTheory.IndepFun (Q.sigma n)
      (fun ω => Wl (Q.toPalmSetting.N.T n ω) ω) Q.toPalmSetting.P0)
    (hGI : ∀ u : ℝ,
      (∫ ω, Complex.exp (Complex.I * u * Q.sigma 0 ω) ∂Q.toPalmSetting.P0)
        = ∫ ω, Complex.exp (Complex.I * u * Q.sigma 0 ω) ∂Q.toPalmSetting.P)
    (hidle : (Q.toPalmSetting.P {ω | W 0 ω = 0}).toReal = 1 - Q.rho)
    (u : ℝ) :
    Complex.I * u * ∫ ω, Complex.exp (Complex.I * u * W 0 ω) ∂Q.toPalmSetting.P
      = (Q.toPalmSetting.lam : ℂ)
          * (∫ ω, Complex.exp (Complex.I * u * Wl 0 ω) ∂Q.toPalmSetting.P0)
          * ((∫ ω, Complex.exp (Complex.I * u * Q.sigma 0 ω) ∂Q.toPalmSetting.P) - 1)
        + Complex.I * u * ((1 : ℂ) - (Q.rho : ℂ)) := by sorry

end PalmQueueing.Formulas
