-- Prove2me | Theorems.Thm_ProjNewton_Superlinear_proposition2
-- name    : ProjNewton.Superlinear.proposition2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T01:31:03.920448+00:00
-- url     : https://prove2.me/theorems/04b73e20-b8b6-46a7-8722-697f24d3bcc8
-- title:
--   Proposition 2 — every limit point is critical
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ be continuously differentiable and suppose its gradient is Lipschitz on each bounded set (Assumption (A)). Let $(x_k)$ be a run of (35) with the prescribed positive definite partly diagonal matrices, and suppose the scaled quadratic-form bounds (41) hold with fixed positive constants and nonnegative integer exponents (Assumption (B)). Then
--
--   $$x_{k_j}\to\bar x\quad\Longrightarrow\quad\bar x\text{ is a critical point of problem (1)}.$$
--
--   Every limit point is therefore stationary for the nonnegative orthant constraint; the proposition does not assert that a limit point exists.
--
--   **Formalization Note** `MapClusterPt` expresses a subsequential limit. Admissibility records the matrix-selection rule from p. 228, and the run records $x_0\ge0$, the first accepted exponent and the update. The standing $C^1$ assumption and $n\ge1$ are explicit.
-- source:
--   Bertsekas, Projected Newton Methods for Optimization Problems with Simple Constraints, SIAM J. Control Optim. 20(2) (1982), p. 230, Proposition 2; Assumptions (A), (B), (40), (41)

import Mathlib
import Definitions.Def_ProjNewton_Superlinear_Algorithm

namespace ProjNewton.Superlinear

open Matrix Filter Topology

/-- Bertsekas (1982), Proposition 2, p. 230. -/
theorem proposition2 {n : ℕ} (hn : 0 < n) (f : Vec n → ℝ)
    (hf : ContDiff ℝ 1 f) (hA : AssumptionA f)
    (μ : Fin n → ℝ) (ε β σ : ℝ) (hpar : Params μ ε β σ)
    (D : ℕ → Matrix (Fin n) (Fin n) ℝ) (x : ℕ → Vec n)
    (hrun : IsRun f μ ε β σ D x)
    (hadm : AdmissibleScaling f μ ε D x)
    (lam1 lam2 : ℝ) (q₁ q₂ : ℕ)
    (hB : AssumptionB f μ D x lam1 lam2 q₁ q₂) :
    ∀ xbar : Vec n, MapClusterPt xbar atTop x → IsCritical f xbar := by sorry

end ProjNewton.Superlinear
