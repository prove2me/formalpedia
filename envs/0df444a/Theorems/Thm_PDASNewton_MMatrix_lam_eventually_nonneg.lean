-- Prove2me | Theorems.Thm_PDASNewton_MMatrix_lam_eventually_nonneg
-- name    : PDASNewton.MMatrix.lam_eventually_nonneg
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:13:13.109438+00:00
-- url     : https://prove2.me/theorems/01c08f1a-be92-497b-b47d-0dd1acee7e9b
-- title:
--   Appendix A and Remark A.1, p. 20 — λ^k̄ᵢ < 0 (k̄ ≥ 1) ⇒ λᵏᵢ = 0, yᵏᵢ ≤ ψᵢ for k ≥ k̄+1; λᵏ ≥ 0 for k ≥ k_o
-- statement:
--   Let $A \in \mathbb{R}^{n\times n}$ be an M-matrix, $f,\psi\in\mathbb{R}^n$, $c > 0$, and let $(y^k,\lambda^k)_{k\ge0}$ be a run of the primal-dual active set algorithm from arbitrary initial data.
--
--   1. (Remark A.1) If $\lambda^{\bar k}_i < 0$ for some $\bar k \ge 1$ and some coordinate $i$, then
--   $$\lambda^k_i = 0 \quad\text{and}\quad y^k_i \le \psi_i \qquad\text{for all } k \ge \bar k + 1 .$$
--
--   2. There exists $k_o$ such that $\lambda^k \ge 0$ for all $k \ge k_o$.
--
--   Eventual dual feasibility gives the convergence of the multipliers in Theorem 3.2.
--
--   **Formalization Note** Remark A.1 is printed without "$\bar k \ge 1$"; its proof in Appendix A assumes it, and the statement fails for $\bar k = 0$ because $(y^0,\lambda^0)$ is arbitrary. The bound is therefore kept.
-- source:
--   Hintermüller, Ito, Kunisch, The primal-dual active set strategy as a semismooth Newton method, HAL hal-01660511v1, p. 20, Appendix A, proof of Theorem 3.2, fourth paragraph, and Remark A.1

import Mathlib
import Definitions.Def_PDASNewton_MMatrix_Setting

open Filter Topology Matrix

namespace PDASNewton.MMatrix

theorem lam_eventually_nonneg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (f ψ : Fin n → ℝ) (c : ℝ)
    (hc : 0 < c) (hA : IsMMatrix A) (y lam : ℕ → Fin n → ℝ) (hrun : PDASNewton.Local.IsRun A f ψ c y lam) :
    (∀ kbar, 1 ≤ kbar → ∀ i, lam kbar i < 0 →
        ∀ k, kbar + 1 ≤ k → lam k i = 0 ∧ y k i ≤ ψ i) ∧
      ∃ k₀, ∀ k, k₀ ≤ k → 0 ≤ lam k := by sorry

end PDASNewton.MMatrix
