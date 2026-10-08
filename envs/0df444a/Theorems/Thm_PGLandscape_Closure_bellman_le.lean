-- Prove2me | Theorems.Thm_PGLandscape_Closure_bellman_le
-- name    : PGLandscape.Closure.bellman_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T05:27:14.707693+00:00
-- url     : https://prove2.me/theorems/fbaa03c3-f5b4-490d-a0bb-8336f3c88ca3
-- title:
--   (5), p. 7 — element-wise inequalities TJ ⪯ T_π J and TJ_π ⪯ J_π
-- statement:
--   Let $(\mathcal S,(\mathcal A_s),g,P,\gamma,\rho)$ be a discounted Markov decision process and $\pi\in\Pi$ a feasible measurable stationary policy, with Bellman operators
--   $(T_\pi J)(s) = g(s,\pi(s))+\gamma\int J\,dP(\cdot\mid s,\pi(s))$ and $(TJ)(s) = \inf_{a\in\mathcal A_s}[g(s,a)+\gamma\int J\,dP(\cdot\mid s,a)]$. Then:
--   1. for every bounded measurable $J:\mathcal S\to\mathbb R$ and every state $s$, $(TJ)(s)\le(T_\pi J)(s)$;
--   2. for every state $s$, $(TJ_\pi)(s)\le J_\pi(s)$, where $J_\pi$ is the cost-to-go of $\pi$.
--
--   In the paper's element-wise notation,
--   $$TJ\preceq T_\pi J\qquad\text{and}\qquad TJ_\pi\preceq J_\pi .$$
--
--   These two inequalities are used throughout: the first compares any policy with the greedy one, the second says that a policy-improvement step never increases cost.
--
--   **Formalization Note** The page's $\mathcal J$ is the set of bounded measurable functions; boundedness also makes the infimum defining $T$ the page's minimum over a family bounded below. $T$ and $T_\pi$ carry the factor $\gamma$, which the page omits in (3)–(4) but uses everywhere else.
-- source:
--   arXiv:1906.01786v3, (5), p. 7

import Mathlib
import Definitions.Def_PGLandscape_Closure_MDP

namespace PGLandscape.Closure

open MeasureTheory ProbabilityTheory

theorem bellman_le {S A : Type*} [MeasurableSpace S] [MeasurableSpace A] (M : MDP S A)
    (π : MPolicy S A) (hπ : IsFeasible M π) :
    (∀ J : S → ℝ, Measurable J → (∃ C : ℝ, ∀ s, |J s| ≤ C) →
        ∀ s, bellmanOpt M J s ≤ bellmanPi M π.1 J s) ∧
      ∀ s, bellmanOpt M (costToGo M π) s ≤ costToGo M π s := by sorry

end PGLandscape.Closure
