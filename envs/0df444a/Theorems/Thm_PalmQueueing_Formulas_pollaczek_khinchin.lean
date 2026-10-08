-- Prove2me | Theorems.Thm_PalmQueueing_Formulas_pollaczek_khinchin
-- name    : PalmQueueing.Formulas.pollaczek_khinchin
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T01:19:50.071928+00:00
-- url     : https://prove2.me/theorems/0f129e7e-c351-4c78-839c-cbd81c871863
-- title:
--   Eq. (3.4.45) — the Pollaczek–Khinchin characteristic function formula
-- statement:
--   **The Pollaczek–Khinchin characteristic function formula.** In an $M/GI/1/\infty$ queue,
--   $$ E[e^{iuW(0)}] = \frac{iu(1-\rho)}{iu - \lambda(\Psi_\sigma(u) - 1)} , \tag{3.4.45} $$
--   where $\Psi_\sigma(u)$ is the characteristic function of $\sigma_0$.
--
--   It is Takács' formula (3.4.44) with one substitution, and that substitution is **PASTA**: when the
--   arrival process is Poisson, the PASTA property gives $E^0_A[e^{iuW(0-)}] = E[e^{iuW(0)}]$, so the
--   Palm expectation on the right of (3.4.44) becomes the stationary one on the left and the equation
--   can be solved for it.
--
--   This is the chapter's own demonstration of why its goal theorem is worth having: the most quoted
--   formula in single-server queueing theory is one application of PASTA to Takács' formula.
--
--   The hypotheses are therefore the hypotheses PASTA needs, not its conclusion — $A$ admits the
--   constant $\mathcal{F}_t$-intensity $\lambda$, and the **left-limit** workload process $\{W(t-)\}$
--   is $\mathcal{F}_t$-predictable (measurable for the predictable $\sigma$-field
--   $\mathcal{P}(\mathcal{F}_t)$) — together with those of (3.4.44), of which (3.4.45) is the special
--   case: $\sigma_n$ is independent of $W(T_n-)$, $E^0_A[e^{iu\sigma_0}] = E[e^{iu\sigma_0}]$, and
--   $P(X(0) = 0) = 1 - \rho$.
--
--   Non-vanishing of the denominator is a **conjunct of the conclusion**, not a hypothesis. Without it
--   the quotient would be a division by zero at exactly the values of $u$ where the formula is being
--   asserted, and the statement would say nothing there.
-- source:
--   Baccelli & Bremaud, Elements of Queueing Theory: Palm Martingale Calculus and Stochastic Recurrences, 2nd ed., Springer 2003, p. 232, Eq. (3.4.45)

import Mathlib
import Definitions.Def_PalmQueueing_Palm_PointProcess
import Definitions.Def_PalmQueueing_Loynes_SingleServerQueue
import Definitions.Def_PalmQueueing_Palm_StochasticIntensity

/-!
# Eq. (3.4.45): the Pollaczek-Khinchin characteristic function formula (§3.4, p.232)
-/

namespace PalmQueueing.Formulas

open MeasureTheory
open PalmQueueing.Palm PalmQueueing.Loynes

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The Pollaczek-Khinchin characteristic function formula**, Eq. (3.4.45) (p.232). In an
`M/GI/1/∞` queue,

`(3.4.45)  E[e^{iuW(0)}] = iu(1 − ρ) / ( iu − λ(Ψ_σ(u) − 1) )`,

where `Ψ_σ(u)` is the characteristic function of `σ_0`.

It is Takács' formula (3.4.44) with one substitution, and that substitution is **PASTA**: when the
arrival process is Poisson, `E⁰_A[e^{iuW(0−)}] = E[e^{iuW(0)}]`, so the Palm expectation on the
right of (3.4.44) becomes the stationary one on the left and the equation can be solved for it.
This is the chapter's own demonstration of why its goal theorem is worth having — the most quoted
formula in single-server queueing theory is one application of it.

The hypotheses are therefore the hypotheses PASTA needs, not its conclusion: `A` admits the
constant `F_t`-intensity `λ`, and the **left-limit** workload process `{W(t−)}` is
`F_t`-predictable (measurable for the predictable σ-field `P(F_t)` of p.55). The second is what
makes an arriving customer's view the time average. The (3.4.44) hypotheses are kept too, since
(3.4.45) is its special case: `σ_n` is independent of `W(T_n−)` (true in an `M/GI/1/∞` queue, whose
services are i.i.d. and independent of the arrivals), `E⁰_A[e^{iuσ_0}] = E[e^{iuσ_0}]`, and
`P(W(0) = 0) = 1 − ρ`.

Non-vanishing of the denominator is a **conjunct of the conclusion**, not a hypothesis: without it
the quotient would be a division by zero and the statement would say nothing at the very values of
`u` where it is asserted. -/
theorem pollaczek_khinchin (Q : Queue Ω) (W Wl : ℝ → Ω → ℝ) (H : History Ω)
    (hW : IsWorkload Q W Wl) (hWmeas : ∀ t, Measurable (W t))
    (hWcomp : IsCompatible Q.toPalmSetting.θ W)
    (hstable : Q.rho < 1)
    (hhist : H.IsHistoryOf Q.toPalmSetting.N)
    (hintensity : HasConstantIntensity H Q.toPalmSetting.N Q.toPalmSetting.P Q.toPalmSetting.lam)
    (hpred : Measurable[H.predictableSigma] fun p : ℝ × Ω => Wl p.1 p.2)
    (hindep : ∀ n : ℤ, ProbabilityTheory.IndepFun (Q.sigma n)
      (fun ω => Wl (Q.toPalmSetting.N.T n ω) ω) Q.toPalmSetting.P0)
    (hidle : (Q.toPalmSetting.P {ω | W 0 ω = 0}).toReal = 1 - Q.rho)
    (hGI : ∀ u : ℝ,
      (∫ ω, Complex.exp (Complex.I * u * Q.sigma 0 ω) ∂Q.toPalmSetting.P0)
        = ∫ ω, Complex.exp (Complex.I * u * Q.sigma 0 ω) ∂Q.toPalmSetting.P)
    (u : ℝ) (hu : u ≠ 0) :
    Complex.I * u
        - (Q.toPalmSetting.lam : ℂ)
          * ((∫ ω, Complex.exp (Complex.I * u * Q.sigma 0 ω) ∂Q.toPalmSetting.P) - 1) ≠ 0 ∧
    (∫ ω, Complex.exp (Complex.I * u * W 0 ω) ∂Q.toPalmSetting.P)
      = (Complex.I * u * ((1 : ℂ) - (Q.rho : ℂ)))
        / (Complex.I * u
            - (Q.toPalmSetting.lam : ℂ)
              * ((∫ ω, Complex.exp (Complex.I * u * Q.sigma 0 ω) ∂Q.toPalmSetting.P) - 1)) := by sorry

end PalmQueueing.Formulas
