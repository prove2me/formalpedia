-- Prove2me | Theorems.Thm_PDASNewton_MMatrix_ystar_le_y
-- name    : PDASNewton.MMatrix.ystar_le_y
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:12:58.181676+00:00
-- url     : https://prove2.me/theorems/b36ba545-bf58-405d-98d1-43c00adaad54
-- title:
--   Appendix A, p. 20 — for an M-matrix, y* ≤ yᵏ for all k ≥ 1
-- statement:
--   Let $A \in \mathbb{R}^{n\times n}$ be an M-matrix, $f,\psi\in\mathbb{R}^n$, $c > 0$, let $(y^*,\lambda^*)$ solve
--   $$Ay^* + \lambda^* = f, \qquad \lambda^* - \max(0, \lambda^* + c(y^*-\psi)) = 0,$$
--   and let $(y^k,\lambda^k)_{k\ge0}$ be a run of the primal-dual active set algorithm from arbitrary initial data. Then
--   $$y^* \le y^k \qquad\text{for every } k \ge 1 .$$
--
--   Together with monotonicity this bounds the primal iterates from below and yields their convergence.
--
--   **Formalization Note** The solution $(y^*,\lambda^*)$ is a hypothesis; for an M-matrix it exists and is unique (Berman–Plemmons), which the paper uses when it speaks of "the unique solution".
-- source:
--   Hintermüller, Ito, Kunisch, The primal-dual active set strategy as a semismooth Newton method, HAL hal-01660511v1, p. 20, Appendix A, proof of Theorem 3.2, third paragraph

import Mathlib
import Definitions.Def_PDASNewton_MMatrix_Setting

open Filter Topology Matrix

namespace PDASNewton.MMatrix

theorem ystar_le_y {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (f ψ : Fin n → ℝ) (c : ℝ)
    (hc : 0 < c) (hA : IsMMatrix A) (ystar lamstar : Fin n → ℝ)
    (hsol : PDASNewton.Local.IsSolution A f ψ c ystar lamstar) (y lam : ℕ → Fin n → ℝ)
    (hrun : PDASNewton.Local.IsRun A f ψ c y lam) :
    ∀ k, 1 ≤ k → ystar ≤ y k := by sorry

end PDASNewton.MMatrix
