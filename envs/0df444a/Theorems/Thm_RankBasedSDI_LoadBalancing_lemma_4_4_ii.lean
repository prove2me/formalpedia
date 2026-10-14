-- Prove2me | Theorems.Thm_RankBasedSDI_LoadBalancing_lemma_4_4_ii
-- name    : RankBasedSDI.LoadBalancing.lemma_4_4_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:31:10.098538+00:00
-- url     : https://prove2.me/theorems/84b8d5df-1bf0-4e5f-9d2f-526354b4c0ff
-- title:
--   Lemma 4.4(ii): $(\hat E^n,\hat S^n)\Rightarrow(E,S)$, independent Brownian motions with coefficients $\mathrm{diag}(\lambda_i^{1/2})$, $\mathrm{diag}(\mu_i^{1/2}\sigma^{ser}_i)$
-- statement:
--   Consider a sequence of load-balancing systems satisfying (2.9)–(2.13). Then
--
--   $$
--   (\hat E^n,\hat S^n)\Rightarrow(E,S)\quad\text{in }D(\mathbb R_+,\mathbb R^{2N}),
--   $$
--
--   where $E$ and $S$ are mutually independent $N$-dimensional Brownian motions starting at zero, with zero drift and diffusion coefficients $\mathrm{diag}(\lambda_i^{1/2})$ and $\mathrm{diag}(\mu_i^{1/2}\sigma^{ser}_i)$ respectively (recall $\lambda_i=\mu_i$). Concretely, $E_i=\lambda_i^{1/2}W_i$ and $S_i=\mu_i^{1/2}\sigma^{ser}_iW'_i$, where $W_1,\dots,W_N,W'_1,\dots,W'_N$ are independent standard Brownian motions.
--
--   This is the functional central limit theorem for the scaled Poisson arrivals and renewal service processes. The diffusion coefficients $\sigma_i$ of the limit come from it.
--
--   **Formalization Note** The limit lives on some probability space $\Omega'$ (`Type`). Weak convergence to a continuous limit is the referenced `CouplingConverges` (Skorokhod-coupling form, equivalent to $J_1$ weak convergence when the limit is continuous). (IC₀) is not assumed (p. 15).
-- source:
--   Atar & Ichiba, Rank-Based Stochastic Differential Inclusions and Diffusion Limits for a Load Balancing Model, arXiv:2409.15121v1, p. 13, Lemma 4.4(ii)

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

theorem lemma_4_4_ii {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (S : LoadBalancingSequence Ω N) (H : HeavyTraffic S) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (W W' : Ω' → ℝ → Fin N → ℝ),
      IsProbabilityMeasure P' ∧
      IsStandardBM P' (fun ω t => Fin.append (W ω t) (W' ω t)) ∧
      CouplingConverges S.P P'
        (fun n ω t => Fin.append (Ehat S n ω t) (Shat S n ω t))
        (fun ω t => Fin.append (fun i => Real.sqrt (H.lam i) * W ω t i)
          (fun i => Real.sqrt (H.mu i) * serviceSD S i * W' ω t i)) := by sorry

end RankBasedSDI.LoadBalancing
