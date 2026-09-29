-- Prove2me | Theorems.Thm_Peng1990_SMP_stochastic_maximum_principle
-- name    : Peng1990.SMP.stochastic_maximum_principle
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T23:36:48.431988+00:00
-- url     : https://prove2.me/theorems/e86561bb-13ff-4c99-96c9-3bc2e20927b8
-- title:
--   Theorem 3 — the general stochastic maximum principle
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space carrying a standard $d$-dimensional Wiener process $B$ with natural filtration $\mathcal F^t$, and consider the control problem (1)–(2) with data $g,\sigma,l,h$ satisfying assumption (3) and a nonempty control domain $U\subseteq\mathbb R^k$. If $(y,u)$ is an optimal pair, then there exist
--   $$(p,K)\in L^2_{\mathcal F}(0,T;\mathbb R^n)\times\big(L^2_{\mathcal F}(0,T;\mathbb R^n)\big)^d,\qquad (P,Q)\in L^2_{\mathcal F}(0,T;\mathbb R^{n,n})\times\big(L^2_{\mathcal F}(0,T;\mathbb R^{n,n})\big)^d,$$
--   with $P,Q_1,\dots,Q_d$ symmetric-matrix valued, such that $(p,K)$ solves the first-order adjoint equation
--   $$-dp=\Big[g_x^*p+\sum_{j}\sigma_x^{j*}K_j+l_x\Big](y(t),u(t))\,dt-\sum_jK_j\,dB^j,\qquad p(T)=h_x(y(T)),$$
--   $(P,Q)$ solves the second-order adjoint equation
--   $$-dP=\Big[g_x^*P+Pg_x+\sum_j\sigma_x^{j*}P\sigma_x^j+\sum_j\sigma_x^{j*}Q_j+\sum_jQ_j\sigma_x^j+H_{xx}(y,u,p,K)\Big]dt-\sum_jQ_j\,dB^j,\qquad P(T)=h_{xx}(y(T)),$$
--   and for every $v\in U$, for almost every $\tau\in[0,T]$, almost surely,
--   $$H\big(y(\tau),v,p(\tau),K(\tau)-P(\tau)\sigma(y(\tau),u(\tau))\big)+\tfrac12\operatorname{tr}\big(\sigma\sigma^*(y(\tau),v)P(\tau)\big)\ge H\big(y(\tau),u(\tau),p(\tau),K(\tau)-P(\tau)\sigma(y(\tau),u(\tau))\big)+\tfrac12\operatorname{tr}\big(\sigma\sigma^*(y(\tau),u(\tau))P(\tau)\big).$$
--   Here $H(x,v,p,K)=l(x,v)+(p,g(x,v))+\sum_j(K_j,\sigma^j(x,v))$.
--
--   This is the maximum principle for stochastic control with control-dependent diffusion and a possibly nonconvex control domain. It reduces to the classical first-order maximum principle when $\sigma$ does not depend on the control.
--
--   **Formalization Note** The adjoint processes are progressive for the natural filtration of $B$; this is what makes the backward equations nontrivial. Optimality is among admissible controls with finite cost. The variational inequality quantifies $v\in U$ first, then almost every $\tau$, then almost every $\omega$. $P$ and $Q_j$ are symmetric at every $(t,\omega)$ with $t\le T$ ($\mathbb R^{n,n}$ is the space of symmetric matrices, p. 973).
-- source:
--   Peng, A General Stochastic Maximum Principle for Optimal Control Problems, SIAM J. Control Optim. 28(4), 1990, https://doi.org/10.1137/0328054, p. 975, Theorem 3 (with (18) on p. 974 and (19), (20) on pp. 974–975)

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_Peng1990_SMP_ControlProblem
import Definitions.Def_Peng1990_SMP_Adjoint

open MeasureTheory ProbabilityTheory Filter Topology Asymptotics
open scoped ENNReal NNReal Matrix

namespace Peng1990.SMP

theorem stochastic_maximum_principle {Ω : Type*} [MeasurableSpace Ω] {n k d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (cp : ControlProblem n k d) (h3 : Assumption3 cp)
    (B : ℝ≥0 → Ω → Fin d → ℝ) (hB : IsStdBrownian P B)
    (y : ℝ≥0 → Ω → Fin n → ℝ) (u : ℝ≥0 → Ω → Fin k → ℝ)
    (hopt : IsOptimalPair cp (brownianFiltration hB) P B y u) :
    ∃ (p : ℝ≥0 → Ω → Fin n → ℝ) (K : Fin d → ℝ≥0 → Ω → Fin n → ℝ)
      (Pm : ℝ≥0 → Ω → Matrix (Fin n) (Fin n) ℝ)
      (Q : Fin d → ℝ≥0 → Ω → Matrix (Fin n) (Fin n) ℝ),
      L2F (brownianFiltration hB) P cp.T p ∧
      (∀ j, L2F (brownianFiltration hB) P cp.T (K j)) ∧
      L2F (brownianFiltration hB) P cp.T (fun s ω => matEntries (Pm s ω)) ∧
      (∀ j, L2F (brownianFiltration hB) P cp.T (fun s ω => matEntries (Q j s ω))) ∧
      (∀ t ≤ cp.T, ∀ ω, (Pm t ω).IsSymm) ∧ (∀ j, ∀ t ≤ cp.T, ∀ ω, (Q j t ω).IsSymm) ∧
      SolvesFirstAdjoint cp (brownianFiltration hB) P B y u p K ∧
      SolvesSecondAdjoint cp (brownianFiltration hB) P B y u p K Pm Q ∧
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
