-- Prove2me | Theorems.Thm_ShorNonsmooth_Subdiff_convex_iff_hessian_posSemidef
-- name    : ShorNonsmooth.Subdiff.convex_iff_hessian_posSemidef
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T15:32:47.574448+00:00
-- url     : https://prove2.me/theorems/537b1429-e38c-42c3-bb2f-a1d9780e0ba1
-- title:
--   Theorem 1.10 — a $C^2$ function is convex iff its Hessian is positive semidefinite
-- statement:
--   Let $f : E_n \to \mathbb{R}$ be twice continuously differentiable, with Hessian $H(x)$ at $x$. Then $f$ is convex if and only if $H(x)$ is positive semidefinite at every point:
--
--   $$
--   f \text{ convex} \iff (H(x)v, v) \ge 0 \quad \text{for all } x, v \in E_n.
--   $$
--
--   This is the classical second-order test for convexity.
--
--   **Formalization Note** $(H(x)v, v)$ is written as the second Fréchet derivative applied twice, `fderiv ℝ (fderiv ℝ f) x v v`; twice continuous differentiability is `ContDiff ℝ 2 f`.
-- source:
--   Shor, Minimization Methods for Non-Differentiable Functions, Springer 1985, p. 11, Theorem 1.10

import Mathlib

namespace ShorNonsmooth.Subdiff

/-- Shor (1985), p. 11, Theorem 1.10: a twice continuously differentiable function `f` on `E_n`
is convex if and only if its Hessian `H(x)` is positive semidefinite at every point `x`, i.e.
`(H(x) v, v) = D²f(x)(v, v) ≥ 0` for all `x` and `v`. -/
theorem convex_iff_hessian_posSemidef {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 2 f) :
    ConvexOn ℝ Set.univ f ↔ ∀ x v : EuclideanSpace ℝ (Fin n), 0 ≤ fderiv ℝ (fderiv ℝ f) x v v := by sorry

end ShorNonsmooth.Subdiff
