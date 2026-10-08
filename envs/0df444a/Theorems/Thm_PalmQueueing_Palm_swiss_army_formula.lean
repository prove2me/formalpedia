-- Prove2me | Theorems.Thm_PalmQueueing_Palm_swiss_army_formula
-- name    : PalmQueueing.Palm.swiss_army_formula
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-10-01T21:34:28.299164+00:00
-- url     : https://prove2.me/theorems/d8b8cbc1-77e9-4e40-b8df-1bccee105dbb
-- title:
--   Theorem 1.3.1 — the Swiss army formula of Palm calculus
-- statement:
--   **Theorem 1.3.1 (the Swiss army formula).** In the setting of §1.3.7 — arrivals
--   $\{T_n\}$ with counting measure $A$ and intensity $\lambda_A$, departures $\{\tau_n\}$ with
--   counting measure $D$ and no ordering assumed, sojourn times $W_n = \tau_n - T_n \ge 0$ (1.3.26)
--   forming a sequence of marks of $A$, the number in system $\{X(t)\}$ with
--   $X(b) - X(a) = A((a,b]) - D((a,b])$ (1.3.27), a non-decreasing corlol integrator $\{B(t)\}$ and a
--   non-negative process $\{Z(t)\}$ — suppose that $\{Z(t)\}, A, D$ and $\{X(t)\}$ are
--   $\theta_t$-compatible, where $\{\theta_t\}$ is a measurable flow on $(\Omega, \mathcal{F}, P)$ and
--   $P$ is $\theta_t$-invariant. Then for all $t$,
--   $$ \lambda_A\, E^0_A \Big[ \int_{(0, W_0]} Z(s)\, dB(s) \Big]
--   \;=\; \frac{1}{t}\, E \Big[ \int_{(0,t]} X(s-)\, Z(s)\, dB(s) \Big] . \tag{1.3.28} $$
--
--   The book's name for it says what it is. Depending on which blade is selected, this one identity
--   gives the main formulas of Palm calculus: with $Z \equiv 1$ and $B(t) = t$ it reads
--   $\lambda_A E^0_A[W_0] = E[X(0)]$, which is **Little's law**; other choices give the inversion
--   formula, the Miyazawa conservation principle and the rate conservation law.
--
--   Two details of the statement are load-bearing. The integrator on **both** sides is $dB$ — not
--   $dA$, not $dD$; $\{B(t)\}$ is introduced two paragraphs above the theorem and shares its symbol
--   with nothing else. And $X(s-)$ is the **left limit**, not $X(s)$: the proof runs through the
--   Stieltjes-Lebesgue integration-by-parts formula
--   $$ (f(t) - f(0))(g(t) - g(0)) = \int_{(0,t]} (f(s-) - f(0))\, dg(s)
--   + \int_{(0,t]} (g(s) - g(0))\, df(s) , \tag{1.3.29} $$
--   which needs the predictable version of the integrand.
--
--   The compatibility of $\{B(t)\}$ with the flow is assumed here although p.29 does not list it among
--   the compatibility hypotheses; the proof uses it at the step "$R(t) = R(0) \circ \theta_t$" (p.30),
--   and without it the identity is false, its left-hand side being independent of $t$ while its
--   right-hand side would not be. The book states the conclusion "for all $t \in \mathbb{R}$"; it is
--   stated here for $t > 0$, the factor $1/t$ requiring $t \ne 0$.
-- source:
--   Baccelli & Bremaud, Elements of Queueing Theory: Palm Martingale Calculus and Stochastic Recurrences, 2nd ed., Springer 2003, p. 29, Theorem 1.3.1, Eq. (1.3.28)

import Mathlib
import Definitions.Def_PalmQueueing_Palm_PointProcess
import Definitions.Def_PalmQueueing_Palm_SwissArmySetting

/-!
# Theorem 1.3.1: the Swiss army formula of Palm calculus (§1.3.7, p.29)
-/

namespace PalmQueueing.Palm

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The Swiss army formula**, Theorem 1.3.1, Eq. (1.3.28) (§1.3.7, p.29). In the setting of
pp.28-29 — arrivals `{T_n}` with counting measure `A` and intensity `λ_A`, departures `{τ_n}` with
counting measure `D` and no ordering assumed, sojourn times `W_n = τ_n - T_n ≥ 0` forming a
sequence of marks of `A`, the number in system `{X(t)}` with `X(b) - X(a) = A((a,b]) - D((a,b])`, a
non-decreasing corlol integrator `{B(t)}` and a non-negative process `{Z(t)}` — for all `t`,

`λ_A E⁰_A [ ∫_{(0, W₀]} Z(s) dB(s) ]  =  (1/t) E [ ∫_{(0, t]} X(s-) Z(s) dB(s) ]`.

The book's name for it says what it is: depending on which blade is selected, this one identity
gives Little's law (`Z ≡ 1`, `B(t) = t`, whereupon it reads `λ_A E⁰_A[W₀] = E[X(0)]`), the
inversion formula, the Miyazawa conservation principle and the rate conservation law.

Two details of the statement are load-bearing. The integrator on **both** sides is `dB`, not `dA`
and not `dD`; and `X(s-)` is the left limit, not `X(s)` — the proof runs through the
Stieltjes-Lebesgue integration by parts formula (1.3.29), which needs the predictable version. -/
theorem swiss_army_formula (S : SwissArmySetting Ω) (t : ℝ) (ht : 0 < t) :
    ENNReal.ofReal S.toPalmSetting.lam *
        ∫⁻ ω, ∫⁻ s in Set.Ioc (0 : ℝ) (S.W 0 ω), ENNReal.ofReal (S.Z s ω)
          ∂((S.B.B ω).measure) ∂S.toPalmSetting.P0
      = (∫⁻ ω, ∫⁻ s in Set.Ioc (0 : ℝ) t, ENNReal.ofReal (S.Xl s ω * S.Z s ω)
          ∂((S.B.B ω).measure) ∂S.toPalmSetting.P) / ENNReal.ofReal t := by sorry

end PalmQueueing.Palm
