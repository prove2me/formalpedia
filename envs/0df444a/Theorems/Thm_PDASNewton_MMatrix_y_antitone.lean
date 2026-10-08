-- Prove2me | Theorems.Thm_PDASNewton_MMatrix_y_antitone
-- name    : PDASNewton.MMatrix.y_antitone
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T02:12:56.371441+00:00
-- url     : https://prove2.me/theorems/66b91da1-6d75-423d-9544-b94195304e76
-- title:
--   Appendix A, p. 20 — for an M-matrix, yᵏ⁺¹ ≤ yᵏ for every k ≥ 1
-- statement:
--   Let $A \in \mathbb{R}^{n\times n}$ be an M-matrix, $f,\psi\in\mathbb{R}^n$, $c > 0$, and let $(y^k,\lambda^k)_{k\ge0}$ be a run of the primal-dual active set algorithm from arbitrary initial data. Then
--   $$y^{k+1} \le y^k \qquad \text{for every } k \ge 1,$$
--   componentwise.
--
--   Monotonicity of the primal iterates is the first half of the global convergence argument of Theorem 3.2.
--
--   **Formalization Note** The inequality is not claimed for $k = 0$: $y^1 \le y^0$ can fail.
-- source:
--   Hintermüller, Ito, Kunisch, The primal-dual active set strategy as a semismooth Newton method, HAL hal-01660511v1, p. 20, Appendix A, proof of Theorem 3.2, first paragraph

import Mathlib
import Definitions.Def_PDASNewton_MMatrix_Setting

open Filter Topology Matrix

namespace PDASNewton.MMatrix

theorem y_antitone {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (f ψ : Fin n → ℝ) (c : ℝ)
    (hc : 0 < c) (hA : IsMMatrix A) (y lam : ℕ → Fin n → ℝ) (hrun : PDASNewton.Local.IsRun A f ψ c y lam) :
    ∀ k, 1 ≤ k → y (k + 1) ≤ y k := by sorry

end PDASNewton.MMatrix
