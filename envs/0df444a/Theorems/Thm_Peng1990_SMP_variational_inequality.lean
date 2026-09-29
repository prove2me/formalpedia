-- Prove2me | Theorems.Thm_Peng1990_SMP_variational_inequality
-- name    : Peng1990.SMP.variational_inequality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T23:35:12.402986+00:00
-- url     : https://prove2.me/theorems/3756ed2c-0e0f-439b-97c4-079387d7b3e0
-- title:
--   Eq. (18) — the second-order variational inequality
-- statement:
--   Assume (3), let $(y,u)$ be optimal, let $(p,K)$ be the first-order adjoint process (13) and $(P,Q)$ the second-order adjoint process (17). Then for every $v\in U$, for almost every $\tau\in[0,T]$, almost surely,
--   $$H\big(y(\tau),v,p(\tau),K(\tau)-P(\tau)\sigma(y(\tau),u(\tau))\big)+\tfrac12\operatorname{tr}\big(\sigma\sigma^*(y(\tau),v)P(\tau)\big)\ \ge\ H\big(y(\tau),u(\tau),p(\tau),K(\tau)-P(\tau)\sigma(y(\tau),u(\tau))\big)+\tfrac12\operatorname{tr}\big(\sigma\sigma^*(y(\tau),u(\tau))P(\tau)\big),\tag{18}$$
--   where $K-P\sigma$ is the tuple $\big(K_j-P\sigma^j\big)_{j=1}^d$. Because $P$ is symmetric, (18) is equivalent to the form printed just before it,
--   $$H(y,v,p,K)-H(y,u,p,K)+\tfrac12\operatorname{tr}\big[(\sigma(y,v)-\sigma(y,u))^*P(\sigma(y,v)-\sigma(y,u))\big]\ge0 .$$
--
--   This is the maximum condition of the stochastic maximum principle, with the second-order correction that appears when the diffusion depends on the control and $U$ is not convex.
--
--   **Formalization Note** "$\forall v\in U$, a.e., a.s." is taken in that order: $v$ is a deterministic point of $U$, then $\tau$ outside a Lebesgue-null subset of $[0,T]$, then $\omega$ outside a $P$-null set; both null sets may depend on $v$.
-- source:
--   Peng, A General Stochastic Maximum Principle for Optimal Control Problems, SIAM J. Control Optim. 28(4), 1990, https://doi.org/10.1137/0328054, p. 974, (18) and the display before it

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_Peng1990_SMP_ControlProblem
import Definitions.Def_Peng1990_SMP_Adjoint

open MeasureTheory ProbabilityTheory Filter Topology Asymptotics
open scoped ENNReal NNReal Matrix

namespace Peng1990.SMP

theorem variational_inequality {Ω : Type*} [MeasurableSpace Ω] {n k d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (cp : ControlProblem n k d) (h3 : Assumption3 cp)
    (B : ℝ≥0 → Ω → Fin d → ℝ) (hB : IsStdBrownian P B)
    (y : ℝ≥0 → Ω → Fin n → ℝ) (u : ℝ≥0 → Ω → Fin k → ℝ)
    (hopt : IsOptimalPair cp (brownianFiltration hB) P B y u)
    (p : ℝ≥0 → Ω → Fin n → ℝ) (K : Fin d → ℝ≥0 → Ω → Fin n → ℝ)
    (hpK : RepresentsI cp (brownianFiltration hB) P B y u p K)
    (Pm : ℝ≥0 → Ω → Matrix (Fin n) (Fin n) ℝ) (Q : Fin d → ℝ≥0 → Ω → Matrix (Fin n) (Fin n) ℝ)
    (hPQ : RepresentsM cp (brownianFiltration hB) P B y u p K Pm Q) :
    ∀ v ∈ cp.U, ∀ᵐ τ ∂(volume.restrict (Set.Icc (0 : ℝ) cp.T)), ∀ᵐ ω ∂P,
      ham cp (y τ.toNNReal ω) (u τ.toNNReal ω) (p τ.toNNReal ω)
          (fun j => K j τ.toNNReal ω
            - Pm τ.toNNReal ω *ᵥ cp.σ j (y τ.toNNReal ω) (u τ.toNNReal ω))
        + (1 / 2 : ℝ) * Matrix.trace
            (sigmaSigmaT cp (y τ.toNNReal ω) (u τ.toNNReal ω) * Pm τ.toNNReal ω)
      ≤ ham cp (y τ.toNNReal ω) v (p τ.toNNReal ω)
          (fun j => K j τ.toNNReal ω
            - Pm τ.toNNReal ω *ᵥ cp.σ j (y τ.toNNReal ω) (u τ.toNNReal ω))
        + (1 / 2 : ℝ) * Matrix.trace (sigmaSigmaT cp (y τ.toNNReal ω) v * Pm τ.toNNReal ω) := by sorry

end Peng1990.SMP
