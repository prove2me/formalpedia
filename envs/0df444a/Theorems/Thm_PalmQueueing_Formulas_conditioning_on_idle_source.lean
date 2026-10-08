-- Prove2me | Theorems.Thm_PalmQueueing_Formulas_conditioning_on_idle_source
-- name    : PalmQueueing.Formulas.conditioning_on_idle_source
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T01:25:05.334999+00:00
-- url     : https://prove2.me/theorems/49ccebc4-e14b-45ea-943a-359462151e94
-- title:
--   Lemma 3.5.1 — a conditional expectation equals a Palm expectation
-- statement:
--   **Lemma 3.5.1.** Under the assumptions of Property 3.5.1,
--   $$ E[W(0) \mid \xi_i(0) = 0] = E^0_{N^i}[W(0)] . \tag{3.5.31} $$
--
--   The mean workload given that source $i$ is **off** at the origin equals the mean workload seen by
--   source $i$ at the instant it **switches on**. That is not a coincidence of the fluid model: it is
--   Papangelou's theorem applied to the $\mathcal{F}^i_t$-intensity of $N^i$.
--
--   The mechanism, from the page. In view of the independence assumptions and of the exponentiality of
--   the off periods, $N^i$ admits the $\mathcal{F}^i_t$-intensity
--   $$ \mu_i(t) = \frac{\lambda_i}{1 - p_i}\mathbf{1}_{\xi^i(t) = 0} ; $$
--   the off periods being exponential is exactly what makes the intensity a function of the current
--   on-off state alone. Papangelou's theorem then gives the density
--   $$ \left.\frac{dP^0_{N^i}}{dP}\right|_{\mathcal{F}_{t-}}
--   = \frac{\mu_i(t)}{E[\mu_i(t)]} = \frac{\mathbf{1}_{\xi^i(t)=0}}{1-p_i} , $$
--   and since $W(t)$ is continuous, $W(0) = W(0-)$, so
--   $E^0_{N^i}[W(0)] = E[W(0)\mathbf{1}_{\xi^i(0)=0}]/(1-p_i) = E[W(0) \mid \xi_i(0) = 0]$.
--
--   **Formalization Note.** The conditional expectation given the event $\{\xi^i(0) = 0\}$ is written
--   as its elementary definition $E[W(0)\mathbf{1}_{\xi^i(0)=0}]/P(\xi^i(0) = 0)$, and both sides are
--   computed in $[0,\infty]$, the workload being non-negative, so no integrability hypothesis is
--   needed.
-- source:
--   Baccelli & Bremaud, Elements of Queueing Theory: Palm Martingale Calculus and Stochastic Recurrences, 2nd ed., Springer 2003, p. 247, Lemma 3.5.1

import Mathlib
import Definitions.Def_PalmQueueing_Palm_PointProcess
import Definitions.Def_PalmQueueing_Formulas_OnOffSources

/-!
# Lemma 3.5.1: a conditional expectation equals a Palm expectation (§3.5.3, p.247)
-/

namespace PalmQueueing.Formulas

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Lemma 3.5.1** (p.247). Under the assumptions of Property 3.5.1,

`(3.5.31)  E[ W(0) | ξ_i(0) = 0 ] = E⁰_{N^i}[ W(0) ]`.

The mean workload given that source `i` is **off** at the origin equals the mean workload seen by
source `i` at the instant it **switches on**. That is not a coincidence of the fluid model: it is
Papangelou's theorem applied to the `F^i_t`-intensity of `N^i`.

The mechanism, from the page. In view of the independence assumptions and of the exponentiality of
the off periods, `N^i` admits the `F^i_t`-intensity `μ_i(t) = λ_i(1 − p_i)^{-1} 1_{ξ^i(t) = 0}`;
the off periods being exponential is exactly what makes the intensity a function of the current
on-off state alone. Papangelou's theorem then gives the density

`dP⁰_{N^i}/dP |_{F_{t−}} = μ_i(t)/E[μ_i(t)] = 1_{ξ^i(t) = 0}/(1 − p_i)`,

and since `W(t)` is continuous (the `F^i_n` are continuous, so `A` has no atoms), `W(0) = W(0−)`, so
`E⁰_{N^i}[W(0)] = E[W(0) 1_{ξ^i(0) = 0}]/(1 − p_i) = E[W(0) | ξ_i(0) = 0]`.

The conditional expectation given the event `{ξ^i(0) = 0}` is written as its elementary definition,
`E[W(0) 1_{ξ^i(0) = 0}] / P(ξ^i(0) = 0)`, and both sides are computed in `ℝ≥0∞`: the workload is
non-negative, so no integrability hypothesis is needed and neither side can take a junk value. -/
theorem conditioning_on_idle_source {k : ℕ} (M : OnOffModel Ω k) (i : Fin k)
    (nu : Fin k → ℝ) (hprop : M.Property351 nu) :
    (∫⁻ ω in {ω | M.xi i 0 ω = 0}, ENNReal.ofReal (M.W 0 ω) ∂M.P) / M.P {ω | M.xi i 0 ω = 0}
      = ∫⁻ ω, ENNReal.ofReal (M.W 0 ω) ∂(M.P0N i) := by sorry

end PalmQueueing.Formulas
