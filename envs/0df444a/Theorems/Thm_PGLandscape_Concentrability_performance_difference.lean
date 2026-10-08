-- Prove2me | Theorems.Thm_PGLandscape_Concentrability_performance_difference
-- name    : PGLandscape.Concentrability.performance_difference
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:29:22.336472+00:00
-- url     : https://prove2.me/theorems/a2366d33-b7ee-4191-ae3f-ce863076db17
-- title:
--   (29), p. 39 — performance difference: ℓ(π) − ℓ(π̄) = ∫ [T_π J_π̄ − J_π̄] dη_π
-- statement:
--   Throughout, $(\mathcal S,(\mathcal A_s)_{s\in\mathcal S},g,P,\gamma,\rho)$ is the discounted Markov decision process of §2 of the paper: states in a measurable space $\mathcal S$, feasible action sets $\mathcal A_s$, a bounded measurable per-period cost $g$, a transition kernel $P(\cdot\mid s,a)$, a discount factor $\gamma\in(0,1)$ and an initial distribution $\rho$. For a measurable stationary policy $\pi$, $J_\pi$ is its cost-to-go, $\eta_\pi=(1-\gamma)\sum_{t\ge0}\gamma^t\Pr^\pi_\rho(s_t\in\cdot)$ its discounted state-occupancy measure and $\ell(\pi)=(1-\gamma)\int J_\pi\,d\rho$ its discounted average cost. $T_\pi J(s)=g(s,\pi(s))+\gamma\int J(s')P(ds'\mid s,\pi(s))$ and $TJ(s)=\min_{a\in\mathcal A_s}[g(s,a)+\gamma\int J(s')P(ds'\mid s,a)]$ are the Bellman operators, $\Pi$ is the set of feasible measurable stationary policies, $\pi^*\in\Pi$ is an optimal policy and $J^*=J_{\pi^*}$.
--
--   For any two measurable stationary policies $\pi$ and $\bar\pi$,
--   $$\ell(\pi)-\ell(\bar\pi)=\int\big[T_\pi J_{\bar\pi}-J_{\bar\pi}\big]\,d\eta_\pi .$$
--
--   This is the cost, normalized form of the performance difference lemma of Kakade and Langford: the gap in average cost between two policies is the occupancy-weighted one-step advantage of $\pi$ over $\bar\pi$. It drives the proofs of Lemma 6, Lemma 8 and Theorem 4.
--
--   **Formalization Note** The paper's middle member, the expectation $(1-\gamma)\mathbb E^\pi_\rho[\sum_t\gamma^t(T_\pi J_{\bar\pi}(s_t)-J_{\bar\pi}(s_t))]$, has no separate object in the formalization and is left out; the statement is the equality of the outer members. Feasibility of $\pi,\bar\pi$ is not needed (costs are bounded on all of $\mathcal S\times\mathcal A$). The paper prints $T_\pi$ and $T$ in (3)–(4) without the factor $\gamma$; every later use (Assumption 2, (6), (7), the proofs) has it, and the formalization includes it.
-- source:
--   arXiv:1906.01786v3, App. D.1, (29), p. 39

import Mathlib
import Definitions.Def_PGLandscape_Closure_MDP

namespace PGLandscape.Concentrability

open MeasureTheory ProbabilityTheory

/-- (29), App. D.1, p. 39 (performance difference lemma): for measurable stationary policies `π`, `π̄`,
`ℓ(π) − ℓ(π̄) = ∫ [T_π J_π̄ − J_π̄] dη_π`. -/
theorem performance_difference {S A : Type*} [MeasurableSpace S] [MeasurableSpace A] (M : PGLandscape.Closure.MDP S A)
    (π πbar : PGLandscape.Closure.MPolicy S A) :
    PGLandscape.Closure.loss M π - PGLandscape.Closure.loss M πbar =
      ∫ s, (PGLandscape.Closure.bellmanPi M π.1 (PGLandscape.Closure.costToGo M πbar) s - PGLandscape.Closure.costToGo M πbar s) ∂(PGLandscape.Closure.occupancy M π) := by sorry

end PGLandscape.Concentrability
