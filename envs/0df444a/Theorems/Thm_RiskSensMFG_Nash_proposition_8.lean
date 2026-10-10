-- Prove2me | Theorems.Thm_RiskSensMFG_Nash_proposition_8
-- name    : RiskSensMFG.Nash.proposition_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:47:01.746983+00:00
-- url     : https://prove2.me/theorems/027b7381-ad62-4c8b-9ffa-7ed98726f6f2
-- title:
--   Proposition 8, p. 27 — the augmented finite-horizon cost of Agent 1 converges when nobody deviates
-- statement:
--   Let $(\pi,\boldsymbol\mu)$ be a mean-field equilibrium, under the standing assumptions and Assumptions 1 and 2, and let $\boldsymbol\Delta$ be the augmented flow. For every horizon $n$,
--   $$\lim_{N\to\infty}\hat J^{(N),n}_1(\boldsymbol\pi^{(N)})=\hat J^n_{\boldsymbol\Delta}(\pi),\qquad\boldsymbol\pi^{(N)}=(\pi,\dots,\pi).$$
--
--   With Proposition 6 this gives the first half of Theorem 4.
--
--   **Formalization Note** The sequence is indexed by $N+1$, so that Agent 1 (index $0$) exists for every term.
-- source:
--   Saldi, Başar & Raginsky, Discrete-time Risk-sensitive Mean-field Games, arXiv:1808.03929v2, p. 27, Proposition 8; proof pp. 27–28

import Mathlib
import Definitions.Def_RiskSensMFG_Nash_Model
import Definitions.Def_RiskSensMFG_Nash_Equilibrium
import Definitions.Def_RiskSensMFG_Nash_Game
import Definitions.Def_RiskSensMFG_Nash_Augmented

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BoundedContinuousFunction

namespace RiskSensMFG.Nash

theorem proposition_8 {X A : Type*} [MetricSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X]
    [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace A] [PolishSpace A] [MeasurableSpace A] [BorelSpace A] [CompactSpace A]
    (M : Model X A) (hS : M.Standing) (h1 : Assumption1 M) (h2a : Assumption2a M)
    (π : MarkovPolicy X A) (μ : ℕ → RiskSensMFG.Existence.PM X) (hmfe : IsMFE M π μ) (h2b : π.WeaklyContinuous) (n : ℕ) :
    Tendsto (fun N : ℕ => JhatN M hS.measurable_c (N + 1) (fun _ => π) 0 n) atTop
      (𝓝 (Jhat M hS.measurable_c (augFlow M hS.measurable_c μ π) π n)) := by sorry

end RiskSensMFG.Nash
