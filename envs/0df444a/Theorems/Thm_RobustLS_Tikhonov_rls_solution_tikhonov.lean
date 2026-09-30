-- Prove2me | Theorems.Thm_RobustLS_Tikhonov_rls_solution_tikhonov
-- name    : RobustLS.Tikhonov.rls_solution_tikhonov
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:32:35.024303+00:00
-- url     : https://prove2.me/theorems/0fb2f78a-d7f8-490b-bd5e-99799a93a945
-- title:
--   Theorem 3.2 — the RLS solution is (µI + AᵀA)⁻¹Aᵀb if µ = (λ − τ)/τ > 0 and A†b else, with µ = ‖Ax − b‖/√(‖x‖² + 1)
-- statement:
--   Let $A \in \mathbb R^{n\times m}$ and $b \in \mathbb R^n$, with Euclidean norms throughout. Let $(x, \lambda, \tau)$ be an optimal point of the second-order cone program (15),
--   $$\text{minimize } \lambda \quad\text{subject to}\quad \|Ax - b\| \le \lambda - \tau,\qquad \left\|\begin{bmatrix} x \\ 1\end{bmatrix}\right\| \le \tau,$$
--   in the variables $x \in \mathbb R^m$, $\lambda, \tau \in \mathbb R$. By Theorem 3.1 of the paper, $x$ is the robust least-squares solution $x_{\rm RLS}$ for perturbation level $\rho = 1$. Put $\mu = (\lambda - \tau)/\tau$. Then
--   $$x = \begin{cases} \big(\mu I + A^\top A\big)^{-1} A^\top b & \text{if } \mu > 0,\\[2pt] A^\dagger b & \text{else,}\end{cases}$$
--   where $A^\dagger b$ is the minimum-norm solution of $Ax = b$, and in both cases
--   $$\mu = \frac{\|Ax - b\|}{\sqrt{\|x\|^2 + 1}}.$$
--
--   The theorem identifies robust least squares with Tikhonov regularization: the robust solution is a ridge-regression solution whose regularization parameter is not chosen by the user but determined by the data through the SOCP (15).
--
--   **Formalization Note** The paper normalizes $\rho = 1$; general $\rho$ follows by scaling (p. 1039). Mathlib has no pseudoinverse, so the branch $\mu \le 0$ asserts that $x$ solves $Ax = b$ with minimum Euclidean norm, which characterizes $A^\dagger b$. The inverse in the branch $\mu > 0$ is Mathlib's matrix inverse; the matrix is positive definite there. Since every feasible $\tau$ satisfies $\tau \ge \sqrt{\|x\|^2+1} \ge 1$, $\mu$ is well defined. The final identity for $\mu$ comes from the last display of the paper's proof and is the claim in the mission's title.
-- source:
--   El Ghaoui & Lebret, Robust Solutions to Least-Squares Problems with Uncertain Data, SIAM J. Matrix Anal. Appl. 18(4):1035–1064 (1997), p. 1040 (PDF p. 6), Theorem 3.2, Eq. (17); identity for µ from the last display of its proof, p. 1041 (PDF p. 7)

import Mathlib
import Definitions.Def_RobustLS_Tikhonov_Core

namespace RobustLS.Tikhonov

open Matrix

/-- **Theorem 3.2** of El Ghaoui & Lebret, *Robust Solutions to Least-Squares Problems with
Uncertain Data*, SIAM J. Matrix Anal. Appl. 18(4) (1997), p. 1040 (PDF p. 6), with the identity
`µ = ‖Ax − b‖/√(‖x‖² + 1)` from the last display of its proof (p. 1041, PDF p. 7):
"When ρ = 1, the (unique) solution x_RLS to the RLS problem is given by
(17) x_RLS = (µI + AᵀA)⁻¹Aᵀb if µ ≜ (λ − τ)/τ > 0, A†b else,
where (λ, τ) are the (unique) optimal points for problem (15)."

Let `(x, λ, τ)` be an optimal point of the SOCP (15)
`minimize λ subject to ‖Ax − b‖ ≤ λ − τ, ‖[x; 1]‖ ≤ τ` (by Theorem 3.1, its `x`-part is the RLS
solution `x_RLS` for `ρ = 1`), and put `µ = (λ − τ)/τ`. Then
* if `µ > 0`, `x = (µI + AᵀA)⁻¹Aᵀb`;
* otherwise, `x = A†b`, i.e. `x` is the minimum-norm solution of `Ax = b`;
* in either case `µ = ‖Ax − b‖/√(‖x‖² + 1)`.

`⁻¹` is Mathlib's matrix inverse; for `µ > 0` the matrix `µI + AᵀA` is positive definite, so this
is the genuine inverse. `τ ≥ √(‖x‖² + 1) ≥ 1` for every feasible point, so the division defining
`µ` is by a positive number. -/
theorem rls_solution_tikhonov {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (b : Fin n → ℝ)
    (x : Fin m → ℝ) (lam tau : ℝ) (hopt : IsSOCPOptimal A b x lam tau) :
    (0 < (lam - tau) / tau →
        x = (((lam - tau) / tau) • (1 : Matrix (Fin m) (Fin m) ℝ) + Aᵀ * A)⁻¹ *ᵥ (Aᵀ *ᵥ b)) ∧
      (¬ 0 < (lam - tau) / tau → IsMinNormSolution A b x) ∧
      (lam - tau) / tau = eucNorm (A *ᵥ x - b) / Real.sqrt (eucNorm x ^ 2 + 1) := by sorry

end RobustLS.Tikhonov
