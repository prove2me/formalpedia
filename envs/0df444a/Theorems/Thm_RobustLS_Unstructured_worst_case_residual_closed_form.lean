-- Prove2me | Theorems.Thm_RobustLS_Unstructured_worst_case_residual_closed_form
-- name    : RobustLS.Unstructured.worst_case_residual_closed_form
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:27:24.200058+00:00
-- url     : https://prove2.me/theorems/3b66ad5f-bcfe-4275-bcc5-80577e1373b2
-- title:
--   Theorem 3.1 — r(A, b, x) = ‖Ax − b‖ + √(‖x‖² + 1), its minimizer is unique, and it is the SOCP (15)
-- statement:
--   Let $n \ge 1$, $A \in \mathbb{R}^{n\times m}$ and $b \in \mathbb{R}^n$, with the Euclidean norm on vectors, and let $r(A,b,x)$ be the worst-case residual (1) with perturbation bound $\rho = 1$ in the Frobenius norm:
--
--   $$
--   r(A,b,x) = \max_{\|[\Delta A\ \Delta b]\|_F \le 1} \|(A+\Delta A)x - (b+\Delta b)\|.
--   $$
--
--   Then:
--
--   1. for every $x \in \mathbb{R}^m$,
--   $$
--   r(A,b,x) = \|Ax-b\| + \sqrt{\|x\|^2+1};
--   $$
--   2. the problem of minimizing $r(A,b,x)$ over $x \in \mathbb{R}^m$ has a unique solution $x_{\mathrm{RLS}}$, the robust least-squares solution;
--   3. this problem is the second-order cone program (15), $\text{minimize } \lambda$ subject to $\|Ax-b\| \le \lambda-\tau$, $\|[x;1]\| \le \tau$: for every $x$, $r(A,b,x)$ is the smallest $\lambda$ for which some $\tau$ makes $(x,\lambda,\tau)$ feasible.
--
--   The closed form turns a max over a matrix ball into two norms, and the SOCP formulation makes the robust least-squares problem solvable by interior-point methods at roughly the cost of a singular value decomposition of $A$.
--
--   **Formalization Note** The paper normalizes $\rho = 1$ ("we take ρ = 1 in what follows"; general $\rho > 0$ follows by the scaling $\phi(A,b,\rho) = \rho\,\phi(A/\rho,b/\rho,1)$, p. 1039). The maximum in (1) is `sSup` of the attained residuals. The hypothesis $n \ge 1$ (at least one equation) is implicit in the paper: for $n = 0$ the worst case is $0$ and item 1 fails. Uniqueness is uniqueness of a global minimizer over all of $\mathbb{R}^m$, and includes its existence.
-- source:
--   El Ghaoui & Lebret, Robust Solutions to Least-Squares Problems with Uncertain Data, SIAM J. Matrix Anal. Appl. 18(4):1035–1064 (1997), p. 1040, Theorem 3.1

import Mathlib
import Definitions.Def_RobustLS_Unstructured_Core

open Matrix

namespace RobustLS.Unstructured

/-- **Theorem 3.1** of El Ghaoui & Lebret, Robust Solutions to Least-Squares Problems with
Uncertain Data, SIAM J. Matrix Anal. Appl. 18(4) (1997), p. 1040 (PDF p. 6). When `ρ = 1`:
(i) the worst-case residual (1) is `r(A, b, x) = ‖Ax − b‖ + √(‖x‖² + 1)` for every `x`;
(ii) minimizing `r(A, b, x)` over `x ∈ ℝ^m` has a unique solution `x_RLS`;
(iii) this problem is the SOCP (15): `r(A, b, x)` is the least `λ` such that
`‖Ax − b‖ ≤ λ − τ` and `‖[x; 1]‖ ≤ τ` for some `τ`.
The assumption `0 < n` (at least one equation) is implicit in the paper; for `n = 0` the
worst-case residual is `0` and (i) fails. -/
theorem worst_case_residual_closed_form {n m : ℕ} (hn : 0 < n) (A : Matrix (Fin n) (Fin m) ℝ)
    (b : Fin n → ℝ) :
    (∀ x : Fin m → ℝ,
      worstCaseResidual A b 1 x = eucNorm (A *ᵥ x - b) + Real.sqrt (eucNorm x ^ 2 + 1)) ∧
    (∃! x : Fin m → ℝ, ∀ y : Fin m → ℝ, worstCaseResidual A b 1 x ≤ worstCaseResidual A b 1 y) ∧
    (∀ x : Fin m → ℝ,
      IsLeast {lam : ℝ | ∃ τ : ℝ, SocpFeasible A b x lam τ} (worstCaseResidual A b 1 x)) := by sorry

end RobustLS.Unstructured
