-- Prove2me | Theorems.Thm_ProjNewton_Superlinear_armijo_rhs_positive
-- name    : ProjNewton.Superlinear.armijo_rhs_positive
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T01:30:36.369726+00:00
-- url     : https://prove2.me/theorems/ae5e228a-9a06-42d5-bcc6-e2771a9a3ae0
-- title:
--   After (37) — positivity of the Armijo right-hand side
-- statement:
--   Fix the paper's algorithm parameters and a feasible point $x$. Let $D$ be symmetric positive definite and diagonal with respect to the enlarged set $I_k^+$ defined by (32). For every trial exponent $m\ge0$, the right-hand side of (37) is nonnegative, and
--
--   $$\operatorname{RHS}_{37}(m)>0\quad\Longleftrightarrow\quad x\text{ is not critical}.$$
--
--   This distinguishes a genuine descent step from a critical fixed point at every trial step.
--
--   **Formalization Note** The factor $\sigma>0$ is retained in the stated right-hand side. The $C^1$ standing assumption, $n\ge1$, feasibility and all parameter ranges are explicit. The displayed $I^+(x)$ here denotes the iteration's enlarged set $I_k^+$, not the smaller set (17).
-- source:
--   Bertsekas, Projected Newton Methods for Optimization Problems with Simple Constraints, SIAM J. Control Optim. 20(2) (1982), p. 229, §2 after (37)

import Mathlib
import Definitions.Def_ProjNewton_Superlinear_Algorithm

namespace ProjNewton.Superlinear

open Matrix Filter Topology

/-- Bertsekas (1982), after (37), p. 229. -/
theorem armijo_rhs_positive {n : ℕ} (hn : 0 < n) (f : Vec n → ℝ)
    (hf : ContDiff ℝ 1 f) (μ : Fin n → ℝ) (ε β σ : ℝ)
    (hpar : Params μ ε β σ) (x : Vec n) (hx : x ∈ orthant n)
    (D : Matrix (Fin n) (Fin n) ℝ) (hD : D.PosDef)
    (hdiag : DiagonalWrt D (Ik f μ ε x)) :
    ∀ m : ℕ, 0 ≤ σ * armijoRHS f μ ε D x (β ^ m) ∧
      (0 < σ * armijoRHS f μ ε D x (β ^ m) ↔ ¬ IsCritical f x) := by sorry

end ProjNewton.Superlinear
