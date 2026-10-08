-- Prove2me | Theorems.Thm_PGLandscape_Concentrability_gap_le_bellman_error_occupancy
-- name    : PGLandscape.Concentrability.gap_le_bellman_error_occupancy
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:29:24.53999+00:00
-- url     : https://prove2.me/theorems/78349407-2573-4d76-bd32-53e25f70fb4a
-- title:
--   Proof of Theorem 4(b), p. 42 — (1 − γ) ∫ (J_π − J*) dρ ≤ ∫ (J_π − TJ_π) dη_{π*} for every π ∈ Π
-- statement:
--   Throughout, $(\mathcal S,(\mathcal A_s)_{s\in\mathcal S},g,P,\gamma,\rho)$ is the discounted Markov decision process of §2 of the paper: states in a measurable space $\mathcal S$, feasible action sets $\mathcal A_s$, a bounded measurable per-period cost $g$, a transition kernel $P(\cdot\mid s,a)$, a discount factor $\gamma\in(0,1)$ and an initial distribution $\rho$. For a measurable stationary policy $\pi$, $J_\pi$ is its cost-to-go, $\eta_\pi=(1-\gamma)\sum_{t\ge0}\gamma^t\Pr^\pi_\rho(s_t\in\cdot)$ its discounted state-occupancy measure and $\ell(\pi)=(1-\gamma)\int J_\pi\,d\rho$ its discounted average cost. $T_\pi J(s)=g(s,\pi(s))+\gamma\int J(s')P(ds'\mid s,\pi(s))$ and $TJ(s)=\min_{a\in\mathcal A_s}[g(s,a)+\gamma\int J(s')P(ds'\mid s,a)]$ are the Bellman operators, $\Pi$ is the set of feasible measurable stationary policies, $\pi^*\in\Pi$ is an optimal policy and $J^*=J_{\pi^*}$.
--
--   Let $\pi^*$ be an optimal policy and assume measurable selection (Assumption 2). Then for every $\pi\in\Pi$,
--   $$(1-\gamma)\int(J_\pi-J^*)\,d\rho\;\le\;\int(J_\pi-TJ_\pi)\,d\eta_{\pi^*}.$$
--
--   The optimality gap $\ell(\pi)-\ell(\pi^*)$ is bounded by the Bellman error of $J_\pi$ weighted by the occupancy measure of the optimal policy. Changing the weighting from $\eta_{\pi^*}$ to $\rho$ is then what part (b) of Theorem 4 pays for with $\|d\eta_{\pi^*}/d\rho\|_\infty$.
--
--   **Formalization Note** Assumption 2 makes $TJ_\pi$ measurable, so the right-hand integral is the paper's. Assumption 1 and the policy class are not needed and are dropped. The paper prints $T_\pi$ and $T$ in (3)–(4) without the factor $\gamma$; every later use (Assumption 2, (6), (7), the proofs) has it, and the formalization includes it.
-- source:
--   arXiv:1906.01786v3, App. D.3, proof of part (b) of Theorem 4, first display up to step (a), p. 42

import Mathlib
import Definitions.Def_PGLandscape_Closure_MDP

namespace PGLandscape.Concentrability

open MeasureTheory ProbabilityTheory

/-- App. D.3, proof of Theorem 4(b), first display through step (a), p. 42: for every `π ∈ Π`,
`(1 − γ) ∫ (J_π − J*) dρ ≤ ∫ (J_π − TJ_π) dη_{π*}`, with `J* = J_{π*}`. -/
theorem gap_le_bellman_error_occupancy {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]
    (M : PGLandscape.Closure.MDP S A) (πstar : PGLandscape.Closure.MPolicy S A) (hopt : PGLandscape.Closure.IsOptimal M πstar) (hA2 : PGLandscape.Closure.Assumption2 M)
    (π : PGLandscape.Closure.MPolicy S A) (hπ : PGLandscape.Closure.IsFeasible M π) :
    (1 - M.γ) * ∫ s, (PGLandscape.Closure.costToGo M π s - PGLandscape.Closure.costToGo M πstar s) ∂M.ρ ≤
      ∫ s, (PGLandscape.Closure.costToGo M π s - PGLandscape.Closure.bellmanOpt M (PGLandscape.Closure.costToGo M π) s) ∂(PGLandscape.Closure.occupancy M πstar) := by sorry

end PGLandscape.Concentrability
