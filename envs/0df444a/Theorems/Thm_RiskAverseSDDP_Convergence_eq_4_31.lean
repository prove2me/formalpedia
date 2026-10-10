-- Prove2me | Theorems.Thm_RiskAverseSDDP_Convergence_eq_4_31
-- name    : RiskAverseSDDP.Convergence.eq_4_31
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-10T03:48:49.057041+00:00
-- url     : https://prove2.me/theorems/f9960c98-5f24-4cb3-8b30-2166137bd2f9
-- title:
--   (4.31), proof of Theorem 4.1, p. 14 — the first-stage gap is bounded by the stage-2 gap at $x^k_{[n_1]}$
-- statement:
--   Consider a run of Algorithm 1 for the problem (3.9) with $T\ge1$ stages, under the standing assumptions and Assumption (H2). Write $\mathfrak Q^{k-1}_1(x_0,\xi_1)$ for the optimal value of the first stage problem with $\mathcal Q_2$ replaced by $\mathcal Q^{k-1}_2$, and $x^k_{[n_1]}=x^k_1$ for the first-stage decision of iteration $k$. Then for every $k\ge1$
--   $$
--   0\le\mathfrak Q_1(x_0,\xi_1)-\mathfrak Q^{k-1}_1(x_0,\xi_1)\le\mathcal Q_2(x^k_{[n_1]})-\mathcal Q^{k-1}_2(x^k_{[n_1]}).\tag{4.31}
--   $$
--
--   With $\mathcal H(2)$ this yields the convergence of the first-stage optimal values in Theorem 4.1 (ii).
--
--   **Formalization Note** Differences are in $\mathbb R\cup\{\pm\infty\}$; while $\mathcal Q^{k-1}_2\equiv-\infty$ both sides are $+\infty$. In Lean the iteration is written $k+1$, so $\mathcal Q^{k-1}_2$ is `Qm k 1`, $\mathfrak Q^{k-1}_1(x_0,\xi_1)$ is `stageVal 0 0 (Qm k 1) (Hist.empty n)` and $\mathfrak Q_1(x_0,\xi_1)=\mathcal Q_1(x_0)$ is `Q1`. For $T=1$, $\mathcal Q_2=\mathcal Q^{k}_2\equiv0$.
-- source:
--   Guigues, Convergence Analysis of Sampling-Based Decomposition Methods for Risk-Averse Multistage Stochastic Convex Programs, arXiv:1408.4439v4, p. 14, (4.30)–(4.31) in the proof of Theorem 4.1

import Mathlib
import Definitions.Def_RiskAverseSDDP_Convergence_Basic
import Definitions.Def_RiskAverseSDDP_Convergence_Model
import Definitions.Def_RiskAverseSDDP_Convergence_Run

namespace RiskAverseSDDP.Convergence

theorem eq_4_31 {T n M q p : ℕ} [NeZero M] (D : Model T n M q p) (ε : ℝ) (hT : 1 ≤ T)
    (hS : D.Standing) (hH2 : D.H2 ε) (R : Rules n M) (ys : ℕ → ℕ → Fin M) (r : RunData n M)
    (hr : D.IsRun R ys r) :
    ∀ k : ℕ,
      0 ≤ D.Q1 - D.stageVal 0 0 (r.Qm k 1) (Hist.empty n) ∧
      D.Q1 - D.stageVal 0 0 (r.Qm k 1) (Hist.empty n) ≤
        D.Q 1 (r.hist (k + 1) 0 Fin.elim0) - r.Qm k 1 (r.hist (k + 1) 0 Fin.elim0) := by sorry

end RiskAverseSDDP.Convergence
