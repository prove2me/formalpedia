-- Prove2me | Theorems.Thm_PGLandscape_Concentrability_sup_norm_error_bound
-- name    : PGLandscape.Concentrability.sup_norm_error_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:29:24.642028+00:00
-- url     : https://prove2.me/theorems/aea41770-6f8e-4933-b394-a8dd78c7d4e7
-- title:
--   (26), p. 37 — ‖J_π − J*‖_∞ ≤ (1/(1 − γ)) ‖J_π − TJ_π‖_∞ for every π ∈ Π
-- statement:
--   Throughout, $(\mathcal S,(\mathcal A_s)_{s\in\mathcal S},g,P,\gamma,\rho)$ is the discounted Markov decision process of §2 of the paper: states in a measurable space $\mathcal S$, feasible action sets $\mathcal A_s$, a bounded measurable per-period cost $g$, a transition kernel $P(\cdot\mid s,a)$, a discount factor $\gamma\in(0,1)$ and an initial distribution $\rho$. For a measurable stationary policy $\pi$, $J_\pi$ is its cost-to-go, $\eta_\pi=(1-\gamma)\sum_{t\ge0}\gamma^t\Pr^\pi_\rho(s_t\in\cdot)$ its discounted state-occupancy measure and $\ell(\pi)=(1-\gamma)\int J_\pi\,d\rho$ its discounted average cost. $T_\pi J(s)=g(s,\pi(s))+\gamma\int J(s')P(ds'\mid s,\pi(s))$ and $TJ(s)=\min_{a\in\mathcal A_s}[g(s,a)+\gamma\int J(s')P(ds'\mid s,a)]$ are the Bellman operators, $\Pi$ is the set of feasible measurable stationary policies, $\pi^*\in\Pi$ is an optimal policy and $J^*=J_{\pi^*}$.
--
--   Let $\pi^*$ be an optimal policy and assume measurable selection (Assumption 2). Then for every $\pi\in\Pi$,
--   $$\|J_\pi-J^*\|_\infty\le\frac1{1-\gamma}\,\|J_\pi-TJ_\pi\|_\infty,\qquad\|J\|_\infty=\sup_{s\in\mathcal S}|J(s)|.$$
--
--   The optimality gap of a policy, measured uniformly over states, is controlled by its Bellman error; this is the consequence of the $\gamma$-contraction of $T$ in the maximum norm on which the definition of $\kappa_\rho$ is modelled.
--
--   **Formalization Note** Both functions are bounded, so the real suprema are the sup norms (if $\mathcal S$ were empty both sides would be $0$). Assumption 2 is needed for $TJ^*=J^*$. The paper prints $T_\pi$ and $T$ in (3)–(4) without the factor $\gamma$; every later use (Assumption 2, (6), (7), the proofs) has it, and the formalization includes it.
-- source:
--   arXiv:1906.01786v3, App. D.1, (26), p. 37

import Mathlib
import Definitions.Def_PGLandscape_Closure_MDP

namespace PGLandscape.Concentrability

open MeasureTheory ProbabilityTheory

/-- (26), App. D.1, p. 37: for every `π ∈ Π`, `‖J_π − J*‖_∞ ≤ (1/(1−γ)) ‖J_π − TJ_π‖_∞`, with
`J* = J_{π*}`. Both families are bounded, so the real suprema are the sup norms. -/
theorem sup_norm_error_bound {S A : Type*} [MeasurableSpace S] [MeasurableSpace A] (M : PGLandscape.Closure.MDP S A)
    (πstar : PGLandscape.Closure.MPolicy S A) (hopt : PGLandscape.Closure.IsOptimal M πstar) (hA2 : PGLandscape.Closure.Assumption2 M)
    (π : PGLandscape.Closure.MPolicy S A) (hπ : PGLandscape.Closure.IsFeasible M π) :
    (⨆ s, |PGLandscape.Closure.costToGo M π s - PGLandscape.Closure.costToGo M πstar s|) ≤
      1 / (1 - M.γ) * ⨆ s, |PGLandscape.Closure.costToGo M π s - PGLandscape.Closure.bellmanOpt M (PGLandscape.Closure.costToGo M π) s| := by sorry

end PGLandscape.Concentrability
