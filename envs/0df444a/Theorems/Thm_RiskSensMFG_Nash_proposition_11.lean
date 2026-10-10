-- Prove2me | Theorems.Thm_RiskSensMFG_Nash_proposition_11
-- name    : RiskSensMFG.Nash.proposition_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:47:00.656986+00:00
-- url     : https://prove2.me/theorems/1ae0f205-c52e-45f1-af78-0672b964532a
-- title:
--   Proposition 11, p. 29 — the augmented finite-horizon cost of a deviating Agent 1 approaches its mean-field cost
-- statement:
--   Let $(\pi,\boldsymbol\mu)$ be a mean-field equilibrium, under the standing assumptions and Assumptions 1 and 2, and let $\{\tilde\pi^{(N)}\}_{N\ge1}$ be an arbitrary sequence of weakly continuous Markov policies for Agent 1. For every horizon $n$,
--   $$\lim_{N\to\infty}\big|\hat J^{(N),n}_1(\tilde\pi^{(N)},\pi,\dots,\pi)-\hat J^n_{\boldsymbol\Delta}(\tilde\pi^{(N)})\big|=0,$$
--   where $\hat J^n_{\boldsymbol\Delta}(\tilde\pi^{(N)})=E[C_{n+1}(\hat s^N(n+1))]$ as in (17).
--
--   With Proposition 6 this gives the second half of Theorem 4.
--
--   **Formalization Note** As in Proposition 9, term $N+1$ of the deviation sequence is used in the game with $N+1$ agents.
-- source:
--   Saldi, Başar & Raginsky, Discrete-time Risk-sensitive Mean-field Games, arXiv:1808.03929v2, p. 29, Proposition 11 and (17)

import Mathlib
import Definitions.Def_RiskSensMFG_Nash_Model
import Definitions.Def_RiskSensMFG_Nash_Equilibrium
import Definitions.Def_RiskSensMFG_Nash_Game
import Definitions.Def_RiskSensMFG_Nash_Augmented

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BoundedContinuousFunction

namespace RiskSensMFG.Nash

theorem proposition_11 {X A : Type*} [MetricSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X]
    [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace A] [PolishSpace A] [MeasurableSpace A] [BorelSpace A] [CompactSpace A]
    (M : Model X A) (hS : M.Standing) (h1 : Assumption1 M) (h2a : Assumption2a M)
    (π : MarkovPolicy X A) (μ : ℕ → RiskSensMFG.Existence.PM X) (hmfe : IsMFE M π μ) (h2b : π.WeaklyContinuous)
    (πt : ℕ → MarkovPolicy X A) (hπt : ∀ N, (πt N).WeaklyContinuous) (n : ℕ) :
    Tendsto (fun N : ℕ =>
        |JhatN M hS.measurable_c (N + 1) (Function.update (fun _ => π) 0 (πt (N + 1))) 0 n -
          Jhat M hS.measurable_c (augFlow M hS.measurable_c μ π) (πt (N + 1)) n|) atTop
      (𝓝 0) := by sorry

end RiskSensMFG.Nash
