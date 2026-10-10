-- Prove2me | Theorems.Thm_RiskAverseSDDP_Convergence_eq_4_26
-- name    : RiskAverseSDDP.Convergence.eq_4_26
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-10T03:49:05.006921+00:00
-- url     : https://prove2.me/theorems/2a83b0e0-ff35-4f19-8fe4-17b4c79ed0a0
-- title:
--   (4.26), proof of Theorem 4.1, p. 13 — on $\mathcal S_n$ the gap at $n$ is bounded by the risk of the gaps at its children
-- statement:
--   Consider a run of Algorithm 1 for the problem (3.9), under the standing assumptions and Assumption (H2). Let $t\in\{2,\dots,T\}$, let $n$ be a node of stage $t-1$, and let $k\ge1$ be an iteration with $k\in\mathcal S_n$, i.e. the scenario sampled at iteration $k$ passes through $n$. Then
--   $$
--   0\le\mathcal Q_t(x^k_{[n]})-\mathcal Q^k_t(x^k_{[n]})\le\sup_{p\in\mathcal P_t}\sum_{m\in C(n)}p_m\Phi_m\Big[\mathcal Q_{t+1}(x^k_{[m]})-\mathcal Q^{k-1}_{t+1}(x^k_{[m]})\Big],\tag{4.26}
--   $$
--   where $C(n)$ is the set of children of $n$.
--
--   This inequality propagates the approximation error backwards along the tree; combined with the induction hypothesis at stage $t+1$ it gives the convergence along the iterations in $\mathcal S_n$.
--
--   **Formalization Note** Differences and the supremum are taken in $\mathbb R\cup\{\pm\infty\}$; while $\mathcal Q^{k-1}_{t+1}\equiv-\infty$ both sides are $+\infty$. The supremum on the right is $\rho_t$ applied to the vector of children's gaps. In Lean the iteration is written $k+1$ (so $\mathcal Q^{k-1}_{t+1}$ is `Qm k (s+2)`), with $t=s+2$, and the child with index $j$ of $\nu$ is `Fin.snoc ν j`.
-- source:
--   Guigues, Convergence Analysis of Sampling-Based Decomposition Methods for Risk-Averse Multistage Stochastic Convex Programs, arXiv:1408.4439v4, p. 13, (4.26) in the proof of Theorem 4.1

import Mathlib
import Definitions.Def_RiskAverseSDDP_Convergence_Basic
import Definitions.Def_RiskAverseSDDP_Convergence_Model
import Definitions.Def_RiskAverseSDDP_Convergence_Run

namespace RiskAverseSDDP.Convergence

theorem eq_4_26 {T n M q p : ℕ} [NeZero M] (D : Model T n M q p) (ε : ℝ)
    (hS : D.Standing) (hH2 : D.H2 ε) (R : Rules n M) (ys : ℕ → ℕ → Fin M) (r : RunData n M)
    (hr : D.IsRun R ys r) :
    ∀ s, s + 2 ≤ T → ∀ (ν : Fin s → Fin M) (k : ℕ), sampNode ys (k + 1) s = ν →
      0 ≤ D.Q (s + 1) (r.hist (k + 1) s ν) - r.Qm (k + 1) (s + 1) (r.hist (k + 1) s ν) ∧
      D.Q (s + 1) (r.hist (k + 1) s ν) - r.Qm (k + 1) (s + 1) (r.hist (k + 1) s ν) ≤
        D.rho (s + 2) (fun j =>
          D.Q (s + 2) (r.hist (k + 1) (s + 1) (Fin.snoc (α := fun _ => Fin M) ν j)) -
            r.Qm k (s + 2) (r.hist (k + 1) (s + 1) (Fin.snoc (α := fun _ => Fin M) ν j))) := by sorry

end RiskAverseSDDP.Convergence
