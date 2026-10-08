-- Prove2me | Theorems.Thm_PGLandscape_Concentrability_bellman_le
-- name    : PGLandscape.Concentrability.bellman_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:29:55.555986+00:00
-- url     : https://prove2.me/theorems/20f081c8-4a81-4919-aa11-f686b4412aa9
-- title:
--   (5), p. 7 — TJ ⪯ T_π J for bounded measurable J, and TJ_π ⪯ J_π, for every π ∈ Π
-- statement:
--   Throughout, $(\mathcal S,(\mathcal A_s)_{s\in\mathcal S},g,P,\gamma,\rho)$ is the discounted Markov decision process of §2 of the paper: states in a measurable space $\mathcal S$, feasible action sets $\mathcal A_s$, a bounded measurable per-period cost $g$, a transition kernel $P(\cdot\mid s,a)$, a discount factor $\gamma\in(0,1)$ and an initial distribution $\rho$. For a measurable stationary policy $\pi$, $J_\pi$ is its cost-to-go, $\eta_\pi=(1-\gamma)\sum_{t\ge0}\gamma^t\Pr^\pi_\rho(s_t\in\cdot)$ its discounted state-occupancy measure and $\ell(\pi)=(1-\gamma)\int J_\pi\,d\rho$ its discounted average cost. $T_\pi J(s)=g(s,\pi(s))+\gamma\int J(s')P(ds'\mid s,\pi(s))$ and $TJ(s)=\min_{a\in\mathcal A_s}[g(s,a)+\gamma\int J(s')P(ds'\mid s,a)]$ are the Bellman operators, $\Pi$ is the set of feasible measurable stationary policies, $\pi^*\in\Pi$ is an optimal policy and $J^*=J_{\pi^*}$.
--
--   Let $\pi\in\Pi$. Then for every bounded measurable $J:\mathcal S\to\mathbb R$, and for the cost-to-go of $\pi$ itself,
--   $$TJ\preceq T_\pi J\qquad\text{and}\qquad TJ_\pi\preceq J_\pi,$$
--   where $\preceq$ is the pointwise order of functions on $\mathcal S$.
--
--   These element-wise inequalities are used throughout the paper; in this mission they give $J_\pi\succeq TJ_\pi$ and $T_{\pi^*}J\succeq TJ$ in the proof of Theorem 4.
--
--   **Formalization Note** The paper prints $T_\pi$ and $T$ in (3)–(4) without the factor $\gamma$; every later use (Assumption 2, (6), (7), the proofs) has it, and the formalization includes it. The statement needs no optimal policy and neither Assumption 1 nor 2.
-- source:
--   arXiv:1906.01786v3, §2, (5), p. 7

import Mathlib
import Definitions.Def_PGLandscape_Closure_MDP

namespace PGLandscape.Concentrability

open MeasureTheory ProbabilityTheory

/-- (5), p. 7: for every `π ∈ Π` and every bounded measurable `J`, `TJ ⪯ T_π J` and `TJ_π ⪯ J_π`. -/
theorem bellman_le {S A : Type*} [MeasurableSpace S] [MeasurableSpace A] (M : PGLandscape.Closure.MDP S A)
    (π : PGLandscape.Closure.MPolicy S A) (hπ : PGLandscape.Closure.IsFeasible M π) :
    (∀ J : S → ℝ, Measurable J → (∃ K : ℝ, ∀ s, |J s| ≤ K) →
      ∀ s, PGLandscape.Closure.bellmanOpt M J s ≤ PGLandscape.Closure.bellmanPi M π.1 J s) ∧
    (∀ s, PGLandscape.Closure.bellmanOpt M (PGLandscape.Closure.costToGo M π) s ≤ PGLandscape.Closure.costToGo M π s) := by sorry

end PGLandscape.Concentrability
