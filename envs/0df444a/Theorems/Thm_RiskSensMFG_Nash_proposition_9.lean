-- Prove2me | Theorems.Thm_RiskSensMFG_Nash_proposition_9
-- name    : RiskSensMFG.Nash.proposition_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:46:52.223019+00:00
-- url     : https://prove2.me/theorems/8292385c-298d-445d-af5c-aa9c43802059
-- title:
--   Proposition 9, p. 28 — propagation of chaos is insensitive to one deviating agent
-- statement:
--   Let $(\pi,\boldsymbol\mu)$ be a mean-field equilibrium, under the standing assumptions and Assumptions 1 and 2, and let $\{\tilde\pi^{(N)}\}_{N\ge1}$ be weakly continuous Markov policies. In the augmented $N$-agent game under $\tilde{\boldsymbol\pi}^{(N)}=(\tilde\pi^{(N)},\pi,\dots,\pi)$ let $\tilde\Delta^{(N)}_t=\frac1N\sum_i\delta_{\tilde s^N_i(t)}$. Then for every $t\ge0$
--   $$\mathcal L(\tilde\Delta^{(N)}_t)\to\delta_{\Delta_t}\quad\text{weakly in }\mathcal P(\mathcal P(\mathsf S)),\ N\to\infty,$$
--   i.e. $E[F(\tilde\Delta^{(N)}_t)]\to F(\Delta_t)$ for every bounded continuous $F$ on $\mathcal P(\mathsf S)$.
--
--   **Formalization Note** The deviating policies are a sequence indexed by $\mathbb N$, of which the term $N+1$ is used in the game with $N+1$ agents; the term $0$ is unused.
-- source:
--   Saldi, Başar & Raginsky, Discrete-time Risk-sensitive Mean-field Games, arXiv:1808.03929v2, p. 28, Proposition 9 (proof referred to [38, Proposition 4.6])

import Mathlib
import Definitions.Def_RiskSensMFG_Nash_Model
import Definitions.Def_RiskSensMFG_Nash_Equilibrium
import Definitions.Def_RiskSensMFG_Nash_Game
import Definitions.Def_RiskSensMFG_Nash_Augmented

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BoundedContinuousFunction

namespace RiskSensMFG.Nash

theorem proposition_9 {X A : Type*} [MetricSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X]
    [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace A] [PolishSpace A] [MeasurableSpace A] [BorelSpace A] [CompactSpace A]
    (M : Model X A) (hS : M.Standing) (h1 : Assumption1 M) (h2a : Assumption2a M)
    (π : MarkovPolicy X A) (μ : ℕ → RiskSensMFG.Existence.PM X) (hmfe : IsMFE M π μ) (h2b : π.WeaklyContinuous)
    (πt : ℕ → MarkovPolicy X A) (hπt : ∀ N, (πt N).WeaklyContinuous) (t : ℕ) (F : RiskSensMFG.Existence.PM (X × ℝ) →ᵇ ℝ) :
    Tendsto (fun N : ℕ => ∫ ω, F (emp (kappa0 M) (fun i => (ω t i).1))
        ∂(augLawN M hS.measurable_c (N + 1) (Function.update (fun _ => π) 0 (πt (N + 1))))) atTop
      (𝓝 (F (augFlow M hS.measurable_c μ π t))) := by sorry

end RiskSensMFG.Nash
