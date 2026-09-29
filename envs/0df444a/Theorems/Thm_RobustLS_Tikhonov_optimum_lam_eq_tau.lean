-- Prove2me | Theorems.Thm_RobustLS_Tikhonov_optimum_lam_eq_tau
-- name    : RobustLS.Tikhonov.optimum_lam_eq_tau
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:29:23.295573+00:00
-- url     : https://prove2.me/theorems/8a9eb89c-ec23-4faf-9c26-82e8d802db81
-- title:
--   Theorem 3.2, proof — if λ = τ at the optimum of (15), then Ax = b and λ = τ = √(‖x‖² + 1)
-- statement:
--   Let $A \in \mathbb R^{n\times m}$, $b \in \mathbb R^n$, and let $(x, \lambda, \tau)$ be an optimal point of the second-order cone program (15),
--   $$\text{minimize } \lambda \quad\text{subject to}\quad \|Ax - b\| \le \lambda - \tau,\qquad \left\|\begin{bmatrix} x \\ 1\end{bmatrix}\right\| \le \tau$$
--   (Euclidean norms). If $\lambda = \tau$, then $x$ solves $Ax = b$ and
--   $$\lambda = \tau = \sqrt{\|x\|^2 + 1}.$$
--
--   This is the degenerate branch of Theorem 3.2: the robust solution fits the data exactly, and both cone constraints of (15) are active.
-- source:
--   El Ghaoui & Lebret, Robust Solutions to Least-Squares Problems with Uncertain Data, SIAM J. Matrix Anal. Appl. 18(4):1035–1064 (1997), p. 1041 (PDF p. 7), Theorem 3.2, proof

import Mathlib
import Definitions.Def_RobustLS_Tikhonov_Core

namespace RobustLS.Tikhonov

open Matrix

/-- El Ghaoui & Lebret, *Robust Solutions to Least-Squares Problems with Uncertain Data*,
SIAM J. Matrix Anal. Appl. 18(4) (1997), Theorem 3.2, proof, p. 1041 (PDF p. 7):
"If λ = τ at the optimum, then Ax = b, and λ = τ = √(‖x‖² + 1)."

If `(x, λ, τ)` is an optimal point of the SOCP (15) and `λ = τ`, then `Ax = b` and
`λ = τ = √(‖x‖² + 1)`. -/
theorem optimum_lam_eq_tau {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin n → ℝ)
    (x : Fin m → ℝ) (lam tau : ℝ) (hopt : IsSOCPOptimal A b x lam tau) (heq : lam = tau) :
    A *ᵥ x = b ∧ lam = Real.sqrt (eucNorm x ^ 2 + 1) ∧ tau = Real.sqrt (eucNorm x ^ 2 + 1) := by sorry

end RobustLS.Tikhonov
