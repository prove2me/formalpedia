-- Prove2me | Theorems.Thm_TegmarkDimensionality_laplacian_radial_profile
-- name    : TegmarkDimensionality.laplacian_radial_profile
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T01:22:39.481461+00:00
-- url     : https://prove2.me/theorems/56228046-54be-40f7-a9ad-9b7505f54ba6
-- title:
--   Mathlib Laplacian of a radial profile $g(\|y\|)$
-- statement:
--   Let $n>2$ and $g:\mathbb R\to\mathbb R$ be twice continuously differentiable. For $x\in\mathbb R^n$ with $x\neq 0$, writing $r=\|x\|$, the Laplacian of the radial function $y\mapsto g(\|y\|)$ satisfies
--   $$\Delta(g\circ\|\cdot\|)(x)=g''(r)+\frac{n-1}{r}g'(r).$$
--
--   This is the standard reduction of the Laplacian to an ordinary differential operator on the radius.
-- source:
--   Classical formula for the Laplacian of a radial function; see e.g. Evans, Partial Differential Equations, Ch. 2

import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.Calculus.FDeriv.Norm

namespace TegmarkDimensionality

open InnerProductSpace Laplacian

/-- For `x ≠ 0`, the Mathlib Laplacian of `y ↦ g (‖y‖)` is the radial second-order term. -/
theorem laplacian_radial_profile (n : ℕ) (hn : 2 < n)
    (g : ℝ → ℝ) (x : EuclideanSpace ℝ (Fin n)) (hx : x ≠ 0)
    (hg : ContDiff ℝ 2 g) :
    Δ (fun y : EuclideanSpace ℝ (Fin n) => g (‖y‖)) x =
      deriv (deriv g) (‖x‖) + ((n : ℝ) - 1) / ‖x‖ * deriv g (‖x‖) := by sorry

end TegmarkDimensionality
