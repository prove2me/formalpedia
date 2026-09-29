-- Prove2me | Theorems.Thm_RobustLS_Unstructured_rls_socp_formulation
-- name    : RobustLS.Unstructured.rls_socp_formulation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T13:27:03.002297+00:00
-- url     : https://prove2.me/theorems/f754ba8c-e160-4dd6-94dc-c342e22b0c7b
-- title:
--   Theorem 3.1, (15) — the RLS problem is the SOCP minimize λ s.t. ‖Ax − b‖ ≤ λ − τ, ‖[x; 1]‖ ≤ τ
-- statement:
--   Let $n \ge 1$, $A \in \mathbb{R}^{n\times m}$ and $b \in \mathbb{R}^n$, and consider the second-order cone program in the variables $x \in \mathbb{R}^m$, $\lambda, \tau \in \mathbb{R}$:
--
--   $$
--   \text{minimize } \lambda \quad \text{subject to} \quad \|Ax-b\| \le \lambda - \tau, \qquad \left\|\begin{bmatrix} x \\ 1 \end{bmatrix}\right\| \le \tau. \tag{15}
--   $$
--
--   Then:
--
--   1. for every $x$, the worst-case residual $r(A,b,x)$ (with $\rho = 1$) is the smallest $\lambda$ for which some $\tau$ makes $(x,\lambda,\tau)$ feasible for (15);
--   2. $x$ minimizes $r(A,b,\cdot)$ over $\mathbb{R}^m$ if and only if there are $\lambda, \tau$ such that $(x,\lambda,\tau)$ is an optimal solution of (15).
--
--   So the robust least-squares problem and the SOCP (15) have the same optimal value and the same optimal $x$.
--
--   **Formalization Note** Optimality in (15) is stated as: $(x,\lambda,\tau)$ is feasible and $\lambda \le \lambda'$ for every feasible $(y,\lambda',\tau')$. The hypothesis $n \ge 1$ is the one of Theorem 3.1.
-- source:
--   El Ghaoui & Lebret, Robust Solutions to Least-Squares Problems with Uncertain Data, SIAM J. Matrix Anal. Appl. 18(4):1035–1064 (1997), p. 1040, Theorem 3.1, Eq. (15)

import Mathlib
import Definitions.Def_RobustLS_Unstructured_Core

open Matrix

namespace RobustLS.Unstructured

/-- El Ghaoui & Lebret (1997), Theorem 3.1, p. 1040 (PDF p. 6), SOCP (15): "This problem can be
formulated as the SOCP minimize λ subject to ‖Ax − b‖ ≤ λ − τ, ‖[x; 1]‖ ≤ τ." For `n ≥ 1` and
`ρ = 1`: (i) for every `x`, `r(A, b, x)` is the least `λ` for which some `τ` makes
`(x, λ, τ)` feasible for (15); (ii) `x` minimizes `r(A, b, ·)` over `ℝ^m` if and only if
`x` is the `x`-part of an optimal solution of (15). -/
theorem rls_socp_formulation {n m : ℕ} (hn : 0 < n) (A : Matrix (Fin n) (Fin m) ℝ)
    (b : Fin n → ℝ) :
    (∀ x : Fin m → ℝ,
      IsLeast {lam : ℝ | ∃ τ : ℝ, SocpFeasible A b x lam τ} (worstCaseResidual A b 1 x)) ∧
    (∀ x : Fin m → ℝ,
      (∀ y : Fin m → ℝ, worstCaseResidual A b 1 x ≤ worstCaseResidual A b 1 y) ↔
        ∃ lam τ : ℝ, SocpFeasible A b x lam τ ∧
          ∀ (y : Fin m → ℝ) (lam' τ' : ℝ), SocpFeasible A b y lam' τ' → lam ≤ lam') := by sorry

end RobustLS.Unstructured
