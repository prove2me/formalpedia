-- Prove2me | Theorems.Thm_RobustLS_Tikhonov_optimal_points_exist
-- name    : RobustLS.Tikhonov.optimal_points_exist
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:28:59.43481+00:00
-- url     : https://prove2.me/theorems/ddc215cc-cca0-4099-864b-7e59fc16c25e
-- title:
--   Theorem 3.2, proof — the SOCP (15) and its dual both have optimal points
-- statement:
--   Let $A \in \mathbb R^{n\times m}$ and $b \in \mathbb R^n$, with Euclidean norms throughout. Consider the second-order cone program (15),
--   $$\text{minimize } \lambda \quad\text{subject to}\quad \|Ax - b\| \le \lambda - \tau,\qquad \left\|\begin{bmatrix} x \\ 1\end{bmatrix}\right\| \le \tau,$$
--   in the variables $x \in \mathbb R^m$, $\lambda, \tau \in \mathbb R$, and its dual
--   $$\text{maximize } b^\top z - v \quad\text{subject to}\quad A^\top z + u = 0,\quad \|z\| \le 1,\quad \left\|\begin{bmatrix} u \\ v\end{bmatrix}\right\| \le 1,$$
--   in the variables $z \in \mathbb R^n$, $u \in \mathbb R^m$, $v \in \mathbb R$. Then both problems attain their optimum: there is a primal optimal point $(x, \lambda, \tau)$ and a dual optimal point $(z, u, v)$.
--
--   The paper deduces this from the strict feasibility of both problems. It guarantees that the optimal points to which Theorem 3.2 refers exist, so that the theorem is not vacuous.
-- source:
--   El Ghaoui & Lebret, Robust Solutions to Least-Squares Problems with Uncertain Data, SIAM J. Matrix Anal. Appl. 18(4):1035–1064 (1997), p. 1041 (PDF p. 7), Theorem 3.2, proof, first sentence

import Mathlib
import Definitions.Def_RobustLS_Tikhonov_Core

namespace RobustLS.Tikhonov

open Matrix

/-- El Ghaoui & Lebret, *Robust Solutions to Least-Squares Problems with Uncertain Data*,
SIAM J. Matrix Anal. Appl. 18(4) (1997), Theorem 3.2, proof, p. 1041 (PDF p. 7):
"Since both primal and dual problems are strictly feasible, there exist optimal points for both
of them."

For every `A ∈ ℝ^{n×m}` and `b ∈ ℝ^n`, the SOCP (15)
`minimize λ subject to ‖Ax − b‖ ≤ λ − τ, ‖[x; 1]‖ ≤ τ`
has an optimal point `(x, λ, τ)`, and its dual
`maximize bᵀz − v subject to Aᵀz + u = 0, ‖z‖ ≤ 1, ‖[u; v]‖ ≤ 1`
has an optimal point `(z, u, v)`. -/
theorem optimal_points_exist {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin n → ℝ) :
    (∃ (x : Fin m → ℝ) (lam tau : ℝ), IsSOCPOptimal A b x lam tau) ∧
      (∃ (z : Fin n → ℝ) (u : Fin m → ℝ) (v : ℝ), IsDualOptimal A b z u v) := by sorry

end RobustLS.Tikhonov
