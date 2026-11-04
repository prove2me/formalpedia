-- Prove2me | Theorems.Thm_RiskAverseSDDP_Convergence_eq_4_33
-- name    : RiskAverseSDDP.Convergence.eq_4_33
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-04T00:08:02.974453+00:00
-- url     : https://prove2.me/theorems/88f3f7c5-ccfd-4d4f-a994-abde36a00472
-- title:
--   (4.33), proof of Theorem 4.1(ii) — accumulation points of $(x^k_{n_1})$ are optimal first-stage solutions
-- statement:
--   This is the accumulation-point part of Theorem 4.1(ii), relation (4.33) and the paragraph after it, in Guigues' convergence analysis of the risk-averse sampling-based decomposition method (Algorithm 1).
--
--   Consider the risk-averse multistage stochastic convex program (3.9) with $T\ge1$ stages, under the standing assumptions on $\Phi_{t,j}$ and $\mathcal P_t$ and Assumption (H2). Take one (deterministic) run of Algorithm 1, with first-stage decisions $x^k_{n_1}$ and approximations $\mathcal Q^k_2$ of $\mathcal Q_2$. Let $\mathfrak Q^{k}_1(x_0,\xi_1)$ be the optimal value of the first-stage problem with $\mathcal Q_2$ replaced by $\mathcal Q^{k}_2$. Assume that
--
--   $$
--   \lim_{k\to+\infty}\mathfrak Q^{k}_1(x_0,\xi_1)=\mathcal Q_1(x_0)
--   \qquad\text{and}\qquad
--   \lim_{k\to+\infty}\mathcal Q_2(x^k_{[n_1]})-\mathcal Q^{k-1}_2(x^k_{[n_1]})=0\quad(4.32).
--   $$
--
--   Then every accumulation point $x^*_{n_1}$ of the sequence $(x^k_{n_1})_k$ is an optimal solution of the first-stage problem (3.12). That is, $x^*_{n_1}\in X_1(x_0,\xi_1)$ and
--
--   $$
--   f_1(x^*_{n_1},\Psi_1)+\mathcal Q_2(x^*_{n_1})=\mathcal Q_1(x_0).
--   $$
--
--   This is the final step of Theorem 4.1. The algorithm's first-stage decisions approach the set of optimal first-stage decisions. The argument passes to the limit in $f_1(x^k_{n_1},\Psi_1)+\mathcal Q^{k-1}_2(x^k_{n_1})=\mathfrak Q^{k-1}_1(x_0,\xi_1)$, using the continuity of $\mathcal Q_2$, the lower semicontinuity of $f_1$, and the closedness of $X_1(x_0,\xi_1)$.
--
--   **Formalization Note** Values are in $\overline{\mathbb R}$ (`EReal`). `stageVal 0 0 (Qm k 1) (Hist.empty n)` is $\mathfrak Q^{k}_1(x_0,\xi_1)$, and `Q1` is $\mathcal Q_1(x_0)$. Hypothesis (4.32) is written with the index shift $k\mapsto k+1$. Accumulation points are cluster points (`MapClusterPt`) of $k\mapsto x^k_{n_1}$ along `atTop`.
-- source:
--   Guigues, Convergence Analysis of Sampling-Based Decomposition Methods for Risk-Averse Multistage Stochastic Convex Programs, arXiv:1408.4439v4, p. 14, proof of Theorem 4.1(ii), eq. (4.33) and the following paragraph

import Mathlib
import Definitions.Def_RiskAverseSDDP_Convergence_Basic
import Definitions.Def_RiskAverseSDDP_Convergence_Model
import Definitions.Def_RiskAverseSDDP_Convergence_Run
open Filter Topology

namespace RiskAverseSDDP.Convergence

theorem eq_4_33 {T n M q p : ℕ} [NeZero M] (D : Model T n M q p) (ε : ℝ) (hT : 1 ≤ T)
    (hS : D.Standing) (hH2 : D.H2 ε) (R : Rules n M) (ys : ℕ → ℕ → Fin M) (r : RunData n M)
    (hr : D.IsRun R ys r)
    (hval : Tendsto (fun k => D.stageVal 0 0 (r.Qm k 1) (Hist.empty n)) atTop (𝓝 D.Q1))
    (h432 : Tendsto
      (fun k => D.Q 1 (r.hist (k + 1) 0 Fin.elim0) - r.Qm k 1 (r.hist (k + 1) 0 Fin.elim0))
      atTop (𝓝 0)) :
    ∀ xs : EuclideanSpace ℝ (Fin n),
      MapClusterPt xs atTop (fun k => r.x k 0 Fin.elim0) → D.IsFirstStageOptimal xs := by sorry

end RiskAverseSDDP.Convergence
