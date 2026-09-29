-- Prove2me | Theorems.Thm_RobustLS_Unstructured_worst_case_residual_strictConvex
-- name    : RobustLS.Unstructured.worst_case_residual_strictConvex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T13:26:36.605764+00:00
-- url     : https://prove2.me/theorems/b9a587db-b1b1-4e04-a724-2d0c6d1b10bf
-- title:
--   Theorem 3.1, proof — the worst-case residual is strictly convex in x
-- statement:
--   Let $n \ge 1$, $A \in \mathbb{R}^{n\times m}$ and $b \in \mathbb{R}^n$. The worst-case residual $x \mapsto r(A,b,x)$ of (1), with $\rho = 1$, is strictly convex on $\mathbb{R}^m$: for all $x \ne y$ and $0 < \theta < 1$,
--
--   $$
--   r\bigl(A,b,\theta x + (1-\theta) y\bigr) < \theta\, r(A,b,x) + (1-\theta)\, r(A,b,y).
--   $$
--
--   This is the property from which the paper derives uniqueness of the robust least-squares solution.
--
--   **Formalization Note** The hypothesis $n \ge 1$ excludes the empty system, for which $r \equiv 0$ is not strictly convex when $m \ge 1$. The paper normalizes $\rho = 1$.
-- source:
--   El Ghaoui & Lebret, Robust Solutions to Least-Squares Problems with Uncertain Data, SIAM J. Matrix Anal. Appl. 18(4):1035–1064 (1997), p. 1040, Theorem 3.1, proof (last sentence)

import Mathlib
import Definitions.Def_RobustLS_Unstructured_Core

open Matrix

namespace RobustLS.Unstructured

/-- El Ghaoui & Lebret (1997), Theorem 3.1, proof, p. 1040 (PDF p. 6): "unicity of the
minimizer x follows from the strict convexity of the worst-case residual". For `n ≥ 1`, the
worst-case residual `x ↦ r(A, b, x)` (with `ρ = 1`) is strictly convex on `ℝ^m`. The
assumption `0 < n` excludes the empty system, where `r ≡ 0`. -/
theorem worst_case_residual_strictConvex {n m : ℕ} (hn : 0 < n) (A : Matrix (Fin n) (Fin m) ℝ)
    (b : Fin n → ℝ) :
    StrictConvexOn ℝ Set.univ (fun x : Fin m → ℝ => worstCaseResidual A b 1 x) := by sorry

end RobustLS.Unstructured
