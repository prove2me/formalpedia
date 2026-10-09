-- Prove2me | Theorems.Thm_SLQSolv_UnifConvex_proposition_4_1
-- name    : SLQSolv.UnifConvex.proposition_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:22:05.828957+00:00
-- url     : https://prove2.me/theorems/c1c8754a-fe61-4e5a-8ad8-fd0f45f4eb8e
-- title:
--   Proposition 4.1, p. 2284 — uniform convexity gives unique open-loop solvability and V⁰(t, x) ≥ α|x|²
-- statement:
--   Assume (H1)–(H2) and suppose $u\mapsto J^0(0,0;u)$ is uniformly convex, i.e. there is $\lambda>0$ with $J^0(0,0;u)\ge\lambda\,\mathbb E\int_0^T|u|^2ds$ for all $u\in\mathcal U[0,T]$. Then Problem (SLQ) is uniquely open-loop solvable at every $(t,x)\in[0,T)\times\mathbb R^n$, and there is a constant $\alpha\in\mathbb R$ such that
--
--   $$V^0(t,x)\ \ge\ \alpha|x|^2\qquad\forall(t,x)\in[0,T]\times\mathbb R^n.\qquad(4.1)$$
--
--   The constant $\alpha$ need not be nonnegative. The bound (4.1) is the lower bound on the Riccati iterates in the proof of Theorem 4.5.
--
--   **Formalization Note** $V^0$ is valued in $[-\infty,\infty)$ (Lean's `EReal`), and $\alpha|x|^2$ is cast to it. Unique solvability is for the full (inhomogeneous) problem, as on the page.
-- source:
--   Sun–Li–Yong, SIAM J. Control Optim. 54 (2016), Proposition 4.1, p. 2284

import Mathlib
import Definitions.Def_SLQSolv_UnifConvex_Riccati

open MeasureTheory Set
open scoped NNReal Matrix

namespace SLQSolv.UnifConvex

/-- Proposition 4.1, p. 2284. If `u ↦ J⁰(0, 0; u)` is uniformly convex, then Problem (SLQ) is
uniquely open-loop solvable, and there is `α ∈ ℝ` with (4.1) `V⁰(t, x) ≥ α|x|²` for all
`(t, x) ∈ [0, T] × ℝⁿ`. -/
theorem proposition_4_1 {Ω : Type*} [MeasurableSpace Ω] {n m : ℕ} (Bs : Basis Ω)
    (d : Data Ω n m) (h1 : H1 Bs d) (h2 : H2 Bs d) (hconv : IsUnifConvex Bs d 0) :
    UniquelyOpenLoopSolvable Bs d ∧
      ∃ α : ℝ, ∀ t ≤ d.T, ∀ x : Fin n → ℝ, ((α * (x ⬝ᵥ x) : ℝ) : EReal) ≤ V0 Bs d t x := by sorry

end SLQSolv.UnifConvex
