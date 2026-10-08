-- Prove2me | Theorems.Thm_PDASNewton_MMatrix_y_le_psi
-- name    : PDASNewton.MMatrix.y_le_psi
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T02:12:49.17651+00:00
-- url     : https://prove2.me/theorems/309baa90-c918-4e24-84fd-3078a1408cdf
-- title:
--   Appendix A, p. 20 — for an M-matrix, yᵏ is feasible, yᵏ ≤ ψ, for all k ≥ 2
-- statement:
--   Let $A \in \mathbb{R}^{n\times n}$ be an M-matrix, $f,\psi\in\mathbb{R}^n$, $c > 0$, and let $(y^k,\lambda^k)_{k\ge0}$ be a run of the primal-dual active set algorithm from arbitrary initial data. Then
--   $$y^k \le \psi \qquad\text{for every } k \ge 2 .$$
--
--   Primal feasibility from the second iterate on is the second ingredient of Theorem 3.2.
--
--   **Formalization Note** The index bound $k \ge 2$ is the paper's; $y^1 \le \psi$ can fail.
-- source:
--   Hintermüller, Ito, Kunisch, The primal-dual active set strategy as a semismooth Newton method, HAL hal-01660511v1, p. 20, Appendix A, proof of Theorem 3.2, second paragraph

import Mathlib
import Definitions.Def_PDASNewton_MMatrix_Setting

open Filter Topology Matrix

namespace PDASNewton.MMatrix

theorem y_le_psi {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (f ψ : Fin n → ℝ) (c : ℝ)
    (hc : 0 < c) (hA : IsMMatrix A) (y lam : ℕ → Fin n → ℝ) (hrun : PDASNewton.Local.IsRun A f ψ c y lam) :
    ∀ k, 2 ≤ k → y k ≤ ψ := by sorry

end PDASNewton.MMatrix
