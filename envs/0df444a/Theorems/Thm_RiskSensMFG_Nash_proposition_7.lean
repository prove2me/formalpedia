-- Prove2me | Theorems.Thm_RiskSensMFG_Nash_proposition_7
-- name    : RiskSensMFG.Nash.proposition_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:47:04.953987+00:00
-- url     : https://prove2.me/theorems/0ab84ddf-d42e-4bdb-b0cb-062ca0c759cb
-- title:
--   Proposition 7, p. 27 — propagation of chaos: L(∆^(N)_t) → δ_{∆_t} weakly when every agent uses π
-- statement:
--   Let $(\pi,\boldsymbol\mu)$ be a mean-field equilibrium, under the standing assumptions and Assumptions 1 and 2. In the augmented $N$-agent game in which every agent uses $\pi$, let $\Delta^{(N)}_t=\frac1N\sum_{i=1}^N\delta_{s^N_i(t)}$. Then for every $t\ge0$
--   $$\mathcal L(\Delta^{(N)}_t)\to\delta_{\Delta_t}\quad\text{weakly in }\mathcal P(\mathcal P(\mathsf S)),\ N\to\infty,$$
--   that is, $E\big[F(\Delta^{(N)}_t)\big]\to F(\Delta_t)$ for every bounded continuous $F:\mathcal P(\mathsf S)\to\mathbb R$.
--
--   The empirical distribution of the augmented states concentrates on the deterministic flow $\boldsymbol\Delta$.
--
--   **Formalization Note** Weak convergence of the laws to a Dirac mass is stated through bounded continuous test functions on $\mathcal P(\mathsf S)$.
-- source:
--   Saldi, Başar & Raginsky, Discrete-time Risk-sensitive Mean-field Games, arXiv:1808.03929v2, p. 27, Proposition 7; proof Appendix B, pp. 32–34

import Mathlib
import Definitions.Def_RiskSensMFG_Nash_Model
import Definitions.Def_RiskSensMFG_Nash_Equilibrium
import Definitions.Def_RiskSensMFG_Nash_Game
import Definitions.Def_RiskSensMFG_Nash_Augmented

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BoundedContinuousFunction

namespace RiskSensMFG.Nash

theorem proposition_7 {X A : Type*} [MetricSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X]
    [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace A] [PolishSpace A] [MeasurableSpace A] [BorelSpace A] [CompactSpace A]
    (M : Model X A) (hS : M.Standing) (h1 : Assumption1 M) (h2a : Assumption2a M)
    (π : MarkovPolicy X A) (μ : ℕ → RiskSensMFG.Existence.PM X) (hmfe : IsMFE M π μ) (h2b : π.WeaklyContinuous) (t : ℕ) (F : RiskSensMFG.Existence.PM (X × ℝ) →ᵇ ℝ) :
    Tendsto (fun N : ℕ => ∫ ω, F (emp (kappa0 M) (fun i => (ω t i).1))
        ∂(augLawN M hS.measurable_c N (fun _ => π))) atTop
      (𝓝 (F (augFlow M hS.measurable_c μ π t))) := by sorry

end RiskSensMFG.Nash
