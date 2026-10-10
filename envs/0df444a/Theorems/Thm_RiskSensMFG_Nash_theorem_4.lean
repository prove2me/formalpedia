-- Prove2me | Theorems.Thm_RiskSensMFG_Nash_theorem_4
-- name    : RiskSensMFG.Nash.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:46:49.537153+00:00
-- url     : https://prove2.me/theorems/68e0dc08-dbff-423c-ba95-0cb5fd0ed801
-- title:
--   Theorem 4, p. 24 — finite-horizon costs of the N-agent game converge to the mean-field costs, with and without a deviating agent
-- statement:
--   Let $(\pi,\boldsymbol\mu)$ be a mean-field equilibrium, under the standing assumptions and Assumptions 1 and 2. For each $N$ let $\tilde\pi^{(N)}$ be an arbitrary weakly continuous Markov policy for Agent 1. Then for every horizon $n$:
--   $$\lim_{N\to\infty}J^{(N),n}_1(\pi,\dots,\pi)=J^n_{\boldsymbol\mu}(\pi),\tag{14}$$
--   $$\lim_{N\to\infty}\big|J^{(N),n}_1(\tilde\pi^{(N)},\pi,\dots,\pi)-J^n_{\boldsymbol\mu}(\tilde\pi^{(N)})\big|=0.\tag{15}$$
--   Here $J^{(N),n}_1(\pi,\dots,\pi)=E^{\boldsymbol\pi^{(N)}}\big[e^{\lambda\sum_{t=0}^n\beta^tc(x^N_1(t),a^N_1(t),e^{(N)}_t)}\big]$ and $J^n_{\boldsymbol\mu}$ is the same finite-horizon cost in the mean-field model with the equilibrium flow.
--
--   This is the finite-horizon approximation from which Corollary 1 and Theorem 3 follow.
--
--   **Formalization Note** The sequences are indexed by $N+1$, so that Agent 1 (index $0$) exists; the deviation sequence is indexed by $\mathbb N$ and its term $N+1$ is used with $N+1$ agents.
-- source:
--   Saldi, Başar & Raginsky, Discrete-time Risk-sensitive Mean-field Games, arXiv:1808.03929v2, p. 24, Theorem 4, (14)–(15); proof p. 29

import Mathlib
import Definitions.Def_RiskSensMFG_Nash_Model
import Definitions.Def_RiskSensMFG_Nash_Equilibrium
import Definitions.Def_RiskSensMFG_Nash_Game

open MeasureTheory ProbabilityTheory Filter Topology

namespace RiskSensMFG.Nash

theorem theorem_4 {X A : Type*} [MetricSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X]
    [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace A] [PolishSpace A] [MeasurableSpace A] [BorelSpace A] [CompactSpace A]
    (M : Model X A) (hS : M.Standing) (h1 : Assumption1 M) (h2a : Assumption2a M)
    (π : MarkovPolicy X A) (μ : ℕ → RiskSensMFG.Existence.PM X) (hmfe : IsMFE M π μ) (h2b : π.WeaklyContinuous)
    (πt : ℕ → MarkovPolicy X A) (hπt : ∀ N, (πt N).WeaklyContinuous) (n : ℕ) :
    Tendsto (fun N : ℕ => JNfin M (N + 1) (fun _ => π) 0 n) atTop
        (𝓝 (Jfin M μ π.toPolicy n)) ∧
      Tendsto (fun N : ℕ => |JNfin M (N + 1) (Function.update (fun _ => π) 0 (πt (N + 1))) 0 n -
          Jfin M μ (πt (N + 1)).toPolicy n|) atTop (𝓝 0) := by sorry

end RiskSensMFG.Nash
