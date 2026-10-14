-- Prove2me | Theorems.Thm_RankBasedSDI_LoadBalancing_proposition_4_1_iii
-- name    : RankBasedSDI.LoadBalancing.proposition_4_1_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:31:16.903781+00:00
-- url     : https://prove2.me/theorems/47460708-4260-4594-be64-c1354479355d
-- title:
--   Proposition 4.1(iii): $(\hat X^n,\hat L^n,\hat B^n)\Rightarrow(X,L,B)$, a weak solution of (SDIR)
-- statement:
--   Consider a sequence of load-balancing systems satisfying (2.9)–(2.13), and assume (IC₀) with limit law $\mu_0$. Let $\hat B^n_i=\sigma_i^{-1}(\hat E^n_i-\hat S^n_i)$. Then there are a stochastic basis $(\Omega',\mathcal F',\mathbb F,P')$ and processes $(X,L,B,\beta)$ on it with the following properties:
--
--   1. $(X,L,B)$ with drift $\beta$ is a weak solution of (SDIR) with the data (2.17), and $X(0)$ has law $\mu_0$;
--   2. the whole sequence converges:
--
--   $$
--   (\hat X^n,\hat L^n,\hat B^n)\Rightarrow(X,L,B)\quad\text{in }D(\mathbb R_+,\mathbb R^{3N})\text{ as }n\to\infty .
--   $$
--
--   This is the diffusion limit for the reflected differential inclusion. Theorem 2.3(i) follows once the limit is also shown to solve (SDER).
--
--   **Formalization Note** The statement takes the existence form. The paper's "the (weak) solution" relies on uniqueness in law, which is not asserted here. The clause "$X(0)$ has law $\mu_0$" is implicit in "solution with initial condition $X_0$" and is made explicit. Weak convergence is the referenced `CouplingConverges`.
-- source:
--   Atar & Ichiba, Rank-Based Stochastic Differential Inclusions and Diffusion Limits for a Load Balancing Model, arXiv:2409.15121v1, p. 11, Proposition 4.1(iii) (standing assumption (IC₀) of §4.1)

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
import Definitions.Def_RankBasedSDI_LoadBalancing_Rank
import Definitions.Def_RankBasedSDI_LoadBalancing_PoissonProcess
import Definitions.Def_RankBasedSDI_LoadBalancing_StochasticBasis
import Definitions.Def_RankBasedSDI_LoadBalancing_Reflection
import Definitions.Def_RankBasedSDI_LoadBalancing_CTight
import Definitions.Def_RankBasedSDI_LoadBalancing_RankBasedEquations
import Definitions.Def_RankBasedSDI_LoadBalancing_Model
import Definitions.Def_RankBasedSDI_LoadBalancing_ScaledProcesses
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open BellWilliams2001.ThresholdPolicy

namespace RankBasedSDI.LoadBalancing

theorem proposition_4_1_iii {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (S : LoadBalancingSequence Ω N) (H : HeavyTraffic S) (μ₀ : ProbabilityMeasure (Fin N → ℝ))
    (hIC : IC0 S μ₀) :
    ∃ (Ω' : Type) (mΩ' : MeasurableSpace Ω') (P' : Measure Ω') (F : Filtration ℝ≥0 mΩ')
      (X L B β : Ω' → ℝ → Fin N → ℝ),
      IsWeakSolutionSDIR (driftB H) (driftM H) (diffSigma H) P' F X L B β ∧
      HasLaw (fun ω => X ω 0) (μ₀ : Measure (Fin N → ℝ)) P' ∧
      CouplingConverges S.P P'
        (fun n ω t => Fin.append (Fin.append (Xhat S n ω t) (Lhat S n ω t)) (Bhat H n ω t))
        (fun ω t => Fin.append (Fin.append (X ω t) (L ω t)) (B ω t)) := by sorry

end RankBasedSDI.LoadBalancing
