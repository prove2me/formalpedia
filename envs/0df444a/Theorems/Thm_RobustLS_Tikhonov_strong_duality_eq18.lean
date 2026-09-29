-- Prove2me | Theorems.Thm_RobustLS_Tikhonov_strong_duality_eq18
-- name    : RobustLS.Tikhonov.strong_duality_eq18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T13:30:25.840795+00:00
-- url     : https://prove2.me/theorems/a0eb2bc1-6b2f-47f4-b5c6-bf1bfbea6b62
-- title:
--   Theorem 3.2, proof, Eq. (18) — equal primal and dual optimal objectives when λ > τ
-- statement:
--   Let $A \in \mathbb R^{n\times m}$ and $b \in \mathbb R^n$ (Euclidean norms). Let $(x, \lambda, \tau)$ be an optimal point of the second-order cone program (15),
--   $$\text{minimize } \lambda \quad\text{subject to}\quad \|Ax - b\| \le \lambda - \tau,\qquad \left\|\begin{bmatrix} x \\ 1\end{bmatrix}\right\| \le \tau,$$
--   with $\lambda > \tau$, and let $(z, u, v)$ be an optimal point of its dual
--   $$\text{maximize } b^\top z - v \quad\text{subject to}\quad A^\top z + u = 0,\quad \|z\| \le 1,\quad \left\|\begin{bmatrix} u \\ v\end{bmatrix}\right\| \le 1.$$
--   Then the primal and dual optimal objectives are equal, in the form of the chain (18):
--   $$\|Ax - b\| + \left\|\begin{bmatrix} x \\ 1\end{bmatrix}\right\| = \lambda = b^\top z - v = -(Ax - b)^\top z - \begin{bmatrix} x^\top & 1\end{bmatrix}\begin{bmatrix} -A^\top z \\ v\end{bmatrix}.$$
--
--   The first equality says both cone constraints of (15) are active at the optimum; the second is strong duality for (15); the third is an algebraic rewriting of the dual objective. The chain is the starting point for identifying the dual optimal point.
--
--   **Formalization Note** The hypothesis $\lambda > \tau$ is the one under which the paper states (18); the equalities in fact hold at every optimal pair.
-- source:
--   El Ghaoui & Lebret, Robust Solutions to Least-Squares Problems with Uncertain Data, SIAM J. Matrix Anal. Appl. 18(4):1035–1064 (1997), p. 1041 (PDF p. 7), Theorem 3.2, proof, Eq. (18)

import Mathlib
import Definitions.Def_RobustLS_Tikhonov_Core

namespace RobustLS.Tikhonov

open Matrix

/-- El Ghaoui & Lebret, *Robust Solutions to Least-Squares Problems with Uncertain Data*,
SIAM J. Matrix Anal. Appl. 18(4) (1997), Theorem 3.2, proof, Eq. (18), p. 1041 (PDF p. 7):
"Now assume λ > τ. Again, both primal and dual problems are strictly feasible; therefore, the
primal- and dual-optimal objectives are equal:
(18) ‖Ax − b‖ + ‖[xᵀ 1]‖ = λ = bᵀz − v = −(Ax − b)ᵀz − [xᵀ 1][−Aᵀz; v]."

If `(x, λ, τ)` is optimal for the SOCP (15) with `λ > τ` and `(z, u, v)` is optimal for its
dual, then the chain of equalities (18) holds. -/
theorem strong_duality_eq18 {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin n → ℝ)
    (x : Fin m → ℝ) (lam tau : ℝ) (z : Fin n → ℝ) (u : Fin m → ℝ) (v : ℝ)
    (hopt : IsSOCPOptimal A b x lam tau) (hlt : tau < lam) (hdual : IsDualOptimal A b z u v) :
    eucNorm (A *ᵥ x - b) + eucNorm (stackOne x) = lam ∧
      lam = b ⬝ᵥ z - v ∧
      b ⬝ᵥ z - v = -((A *ᵥ x - b) ⬝ᵥ z) - stackOne x ⬝ᵥ stackScalar (-(Aᵀ *ᵥ z)) v := by sorry

end RobustLS.Tikhonov
