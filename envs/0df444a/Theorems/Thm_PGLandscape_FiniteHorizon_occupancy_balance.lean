-- Prove2me | Theorems.Thm_PGLandscape_FiniteHorizon_occupancy_balance
-- name    : PGLandscape.FiniteHorizon.occupancy_balance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:28:00.075139+00:00
-- url     : https://prove2.me/theorems/ebd35533-f5e1-4b37-a1c2-66182d702790
-- title:
--   Lemma 17, p. 38 — balance equation: η_π(ℳ) = ∫ [(1 − γ)ρ(ℳ) + γP(ℳ|s, π(s))] η_π(ds)
-- statement:
--   Let $(\mathcal S,(\mathcal A_s),g,P,\gamma,\rho)$ be a discounted Markov decision process and $\pi$ a measurable stationary policy, with discounted state-occupancy measure $\eta_\pi=(1-\gamma)\sum_{t\ge0}\gamma^t P^\pi_\rho(s_t\in\cdot)$. Then for every measurable set $\mathcal M\subseteq\mathcal S$,
--   $$\eta_\pi(\mathcal M)=\int_{\mathcal S}\big[(1-\gamma)\rho(\mathcal M)+\gamma P(\mathcal M\mid s,\pi(s))\big]\,\eta_\pi(ds).$$
--
--   Since $\eta_\pi$ is a probability measure, this is $\eta_\pi(\mathcal M)=(1-\gamma)\rho(\mathcal M)+\gamma\int P(\mathcal M\mid s,\pi(s))\,\eta_\pi(ds)$: the occupancy measure is the fixed point of a restart-and-step operator. It is the basic identity relating occupancy measures to one-step transitions.
--
--   **Formalization Note** The integral of the nonnegative integrand is a Lebesgue integral in $[0,\infty]$, and the coefficients $1-\gamma$, $\gamma$ enter as extended nonnegative reals. The page states the identity "for all $\mathcal M\subset\mathcal S$"; it is formalized for measurable $\mathcal M$. It holds for every measurable stationary policy, feasible or not.
-- source:
--   arXiv:1906.01786v3, Lemma 17, App. D.1, p. 38

import Mathlib
import Definitions.Def_PGLandscape_Closure_MDP

namespace PGLandscape.FiniteHorizon

open MeasureTheory ProbabilityTheory

/-- Lemma 17 (balance equation), arXiv:1906.01786v3, p. 38: for every measurable stationary policy
`π` and every measurable `M ⊆ S`,
`η_π(M) = ∫_S [(1 − γ) ρ(M) + γ P(M | s, π(s))] η_π(ds)`. -/
theorem occupancy_balance {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]
    (M : PGLandscape.Closure.MDP S A) (π : PGLandscape.Closure.MPolicy S A) (B : Set S) (hB : MeasurableSet B) :
    PGLandscape.Closure.occupancy M π B =
      ∫⁻ s, (ENNReal.ofReal (1 - M.γ) * M.ρ B + ENNReal.ofReal M.γ * PGLandscape.Closure.stepKernel M π s B)
        ∂(PGLandscape.Closure.occupancy M π) := by sorry

end PGLandscape.FiniteHorizon
