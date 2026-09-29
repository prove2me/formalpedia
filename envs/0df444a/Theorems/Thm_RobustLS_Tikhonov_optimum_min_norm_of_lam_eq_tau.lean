-- Prove2me | Theorems.Thm_RobustLS_Tikhonov_optimum_min_norm_of_lam_eq_tau
-- name    : RobustLS.Tikhonov.optimum_min_norm_of_lam_eq_tau
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:29:58.813129+00:00
-- url     : https://prove2.me/theorems/7a13606c-e5ee-4e1c-b93a-468e07e57601
-- title:
--   Theorem 3.2, proof — if λ = τ at the optimum of (15), then x = A†b is the minimum-norm solution of Ax = b
-- statement:
--   Let $A \in \mathbb R^{n\times m}$, $b \in \mathbb R^n$, and let $(x, \lambda, \tau)$ be an optimal point of the second-order cone program (15),
--   $$\text{minimize } \lambda \quad\text{subject to}\quad \|Ax - b\| \le \lambda - \tau,\qquad \left\|\begin{bmatrix} x \\ 1\end{bmatrix}\right\| \le \tau$$
--   (Euclidean norms). If $\lambda = \tau$, then $x$ is the minimum-norm solution of $Ax = b$:
--   $$Ax = b \qquad\text{and}\qquad \|x\| \le \|y\| \ \text{ for every } y \in \mathbb R^m \text{ with } Ay = b,$$
--   that is, $x = A^\dagger b$ with $A^\dagger$ the Moore–Penrose pseudoinverse of $A$.
--
--   This is the second branch ("else") of formula (17) in Theorem 3.2.
--
--   **Formalization Note** $A^\dagger b$ is expressed by its characterization as the minimum-norm solution of the (here consistent) system $Ax = b$; Mathlib has no matrix pseudoinverse.
-- source:
--   El Ghaoui & Lebret, Robust Solutions to Least-Squares Problems with Uncertain Data, SIAM J. Matrix Anal. Appl. 18(4):1035–1064 (1997), p. 1041 (PDF p. 7), Theorem 3.2, proof

import Mathlib
import Definitions.Def_RobustLS_Tikhonov_Core

namespace RobustLS.Tikhonov

open Matrix

/-- El Ghaoui & Lebret, *Robust Solutions to Least-Squares Problems with Uncertain Data*,
SIAM J. Matrix Anal. Appl. 18(4) (1997), Theorem 3.2, proof, p. 1041 (PDF p. 7):
"In this case, the optimal x is the (unique) minimum-norm solution to Ax = b: x = A†b."

"This case" is `λ = τ` at the optimum of the SOCP (15). If `(x, λ, τ)` is optimal for (15) and
`λ = τ`, then `x` is a minimum-norm solution of `Ax = b` (i.e. `x = A†b`; the minimum-norm
solution of a consistent system is unique, so `IsMinNormSolution` pins down `A†b`). -/
theorem optimum_min_norm_of_lam_eq_tau {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (b : Fin n → ℝ) (x : Fin m → ℝ) (lam tau : ℝ) (hopt : IsSOCPOptimal A b x lam tau)
    (heq : lam = tau) :
    IsMinNormSolution A b x := by sorry

end RobustLS.Tikhonov
