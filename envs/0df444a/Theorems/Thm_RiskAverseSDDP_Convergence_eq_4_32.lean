-- Prove2me | Theorems.Thm_RiskAverseSDDP_Convergence_eq_4_32
-- name    : RiskAverseSDDP.Convergence.eq_4_32
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-04T00:08:24.031351+00:00
-- url     : https://prove2.me/theorems/d5bab1e7-89b5-4037-8289-dba04021da96
-- title:
--   (4.32), proof of Theorem 4.1(ii) — under $\mathcal H(2)$, $\mathcal Q_2(x^k_{[n_1]})-\mathcal Q^{k-1}_2(x^k_{[n_1]})\to0$
-- statement:
--   This is relation (4.32) in the proof of Theorem 4.1(ii) of Guigues' convergence analysis of the risk-averse sampling-based decomposition method (Algorithm 1).
--
--   Consider the risk-averse multistage stochastic convex program (3.9) with $T\ge1$ stages, under the standing assumptions on $\Phi_{t,j}$ and $\mathcal P_t$ and Assumption (H2). Take one (deterministic) run of Algorithm 1, with first-stage decisions $x^k_{n_1}$ and approximate recourse functions $\mathcal Q^k_2$ of $\mathcal Q_2$. Write $x^k_{[n_1]}=x^k_{n_1}$ for the first-stage decision history. Assume that $\mathcal H(2)$ holds along this run:
--
--   $$
--   \lim_{k\to+\infty}\mathcal Q_2(x^k_{[n_1]})-\mathcal Q^k_2(x^k_{[n_1]})=0 .
--   $$
--
--   Then the gap remains asymptotically zero when the approximation of the previous iteration is used:
--
--   $$
--   \lim_{k\to+\infty}\mathcal Q_2(x^k_{[n_1]})-\mathcal Q^{k-1}_2(x^k_{[n_1]})=0 .
--   $$
--
--   Together with (4.31), this gives the convergence of the first-stage optimal values $\mathfrak Q^{k-1}_1(x_0,\xi_1)\to\mathcal Q_1(x_0)$. It is also the input to the accumulation-point argument (4.33). In the paper it follows from $\mathcal H(2)$ by Lemma A.1 of Girardeau–Leclère–Philpott, which uses the monotonicity $\mathcal Q^{k-1}_2\le\mathcal Q^k_2\le\mathcal Q_2$, the uniform Lipschitz continuity of $\mathcal Q^k_2$ (Lemma 3.5), the continuity of $\mathcal Q_2$ (Proposition 3.1), and the compactness of $\mathcal X_1$.
--
--   **Formalization Note** Gaps are differences in $\overline{\mathbb R}=\mathbb R\cup\{\pm\infty\}$ (`EReal`). `Q 1` is $\mathcal Q_2$ and `Qm k 1` is $\mathcal Q^k_2$, both as functions of the history $x_{1:1}$. The statement is written with the index shift $k\mapsto k+1$: $\mathcal Q_2(x^{k+1}_{[n_1]})-\mathcal Q^{k}_2(x^{k+1}_{[n_1]})\to0$.
-- source:
--   Guigues, Convergence Analysis of Sampling-Based Decomposition Methods for Risk-Averse Multistage Stochastic Convex Programs, arXiv:1408.4439v4, p. 14, proof of Theorem 4.1(ii), eq. (4.32) (via Lemma A.1 of Girardeau-Leclere-Philpott, Math. Oper. Res. 2015)

import Mathlib
import Definitions.Def_RiskAverseSDDP_Convergence_Basic
import Definitions.Def_RiskAverseSDDP_Convergence_Model
import Definitions.Def_RiskAverseSDDP_Convergence_Run
open Filter Topology

namespace RiskAverseSDDP.Convergence

theorem eq_4_32 {T n M q p : ℕ} [NeZero M] (D : Model T n M q p) (ε : ℝ) (hT : 1 ≤ T)
    (hS : D.Standing) (hH2 : D.H2 ε) (R : Rules n M) (ys : ℕ → ℕ → Fin M) (r : RunData n M)
    (hr : D.IsRun R ys r)
    (hH2t : Tendsto (fun k => D.Q 1 (r.hist k 0 Fin.elim0) - r.Qm k 1 (r.hist k 0 Fin.elim0))
      atTop (𝓝 0)) :
    Tendsto (fun k => D.Q 1 (r.hist (k + 1) 0 Fin.elim0) - r.Qm k 1 (r.hist (k + 1) 0 Fin.elim0))
      atTop (𝓝 0) := by sorry

end RiskAverseSDDP.Convergence
