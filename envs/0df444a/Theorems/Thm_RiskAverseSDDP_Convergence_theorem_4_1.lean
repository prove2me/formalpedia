-- Prove2me | Theorems.Thm_RiskAverseSDDP_Convergence_theorem_4_1
-- name    : RiskAverseSDDP.Convergence.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-10T03:50:13.641187+00:00
-- url     : https://prove2.me/theorems/259e1ae9-1f18-4016-a930-b91850162da9
-- title:
--   Theorem 4.1 — almost sure convergence of Algorithm 1: $\mathcal Q_t(x^k_{[n]})-\mathcal Q^k_t(x^k_{[n]})\to0$, first-stage values converge, accumulation points are optimal
-- statement:
--   Consider the risk-averse multistage stochastic convex program (3.9) with $T\ge1$ stages and its dynamic programming equations (3.10)–(3.11), under the interstage independence (H1) with the standing assumptions on $\Phi_{t,j}$ and $\mathcal P_t$, and Assumption (H2). Run Algorithm 1 with fixed deterministic choice rules on random samples $\xi^k_t$ satisfying Assumption (H3) on a probability space $(\Omega,\mathcal F,\mathbb P)$, producing decisions $x^k_n$ at every node $n$ and approximate recourse functions $\mathcal Q^k_t$. Then:
--
--   1. almost surely, for $t=2,\dots,T+1$, the following holds:
--   $$
--   \mathcal H(t):\qquad\forall n\in\mathtt{Nodes}(t-1),\qquad\lim_{k\to+\infty}\mathcal Q_t(x^k_{[n]})-\mathcal Q^k_t(x^k_{[n]})=0;
--   $$
--   2. almost surely, $\lim_{k\to+\infty}\mathfrak Q^k_1(x_0,\xi_1)=\mathcal Q_1(x_0)$, and any accumulation point of the sequence $(x^k_1)_{k\in\mathbb N^*}$ is an optimal solution of the first stage problem (3.12).
--
--   Here $\mathfrak Q^k_1(x_0,\xi_1)$ is the optimal value of the first stage problem with $\mathcal Q_2$ replaced by $\mathcal Q^k_2$. The theorem establishes that the risk-averse sampling-based decomposition algorithm (a risk-averse variant of SDDP for convex, possibly nonlinear, stage problems) computes the optimal value and an optimal first-stage decision in the limit.
--
--   **Formalization Note** The cut slope $\pi_{k,m}$ of Algorithm 1 is modelled as any subgradient of $\mathfrak Q^{k-1}_t(\cdot,\xi_m)$ at the trial point; the printed formula (p. 9) uses a partial subgradient of $f_t$, which is not a subgradient for nonsmooth $f_t$, while the proof only uses the subgradient property. $\mathcal P_t\ne\emptyset$, implicit in the paper, is a standing assumption. (H1) is built into the model (product scenario tree, data indexed by stage and realization). The run is produced by fixed rules from the samples, hence uses only present and past samples. Limits are in $\mathbb R\cup\{\pm\infty\}$; convergence to $0$ forces the gaps to be eventually finite, and $\mathcal Q^k_t\equiv-\infty$ for small $k$ does not trivialize anything. In Lean, (i) is stated for nodes $\nu\in(\mathrm{Fin}\,M)^s$ of stage $s+1=t-1$, $s<T$, with `Q (s+1)` $=\mathcal Q_t$ and `Qm k (s+1)` $=\mathcal Q^k_t$.
-- source:
--   Guigues, Convergence Analysis of Sampling-Based Decomposition Methods for Risk-Averse Multistage Stochastic Convex Programs, arXiv:1408.4439v4, p. 12, Theorem 4.1

import Mathlib
import Definitions.Def_RiskAverseSDDP_Convergence_Basic
import Definitions.Def_RiskAverseSDDP_Convergence_Model
import Definitions.Def_RiskAverseSDDP_Convergence_Run
import Definitions.Def_RiskAverseSDDP_Convergence_Sampling
open Filter Topology MeasureTheory ProbabilityTheory

namespace RiskAverseSDDP.Convergence

theorem theorem_4_1 {T n M q p : ℕ} [NeZero M] (D : Model T n M q p) (ε : ℝ) (hT : 1 ≤ T)
    (hS : D.Standing) (hH2 : D.H2 ε) (R : Rules n M) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ξ : ℕ → Ω → ℕ → Fin M) (hH3 : D.H3 P ξ)
    (r : Ω → RunData n M) (hr : ∀ ω, D.IsRun R (fun k t => ξ k ω t) (r ω)) :
    ∀ᵐ ω ∂P,
      (∀ s, s < T → ∀ ν : Fin s → Fin M,
        Tendsto (fun k => D.Q (s + 1) ((r ω).hist k s ν) - (r ω).Qm k (s + 1) ((r ω).hist k s ν))
          atTop (𝓝 0)) ∧
      Tendsto (fun k => D.stageVal 0 0 ((r ω).Qm k 1) (Hist.empty n)) atTop (𝓝 D.Q1) ∧
      ∀ xs : EuclideanSpace ℝ (Fin n),
        MapClusterPt xs atTop (fun k => (r ω).x k 0 Fin.elim0) → D.IsFirstStageOptimal xs := by sorry

end RiskAverseSDDP.Convergence
