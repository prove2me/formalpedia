-- Prove2me | Theorems.Thm_TegmarkDimensionality_asgeirsson_mean_value_positive_radius
-- name    : TegmarkDimensionality.asgeirsson_mean_value_positive_radius
-- status  : Open
-- author  : @moona3k
-- created : 2026-10-04T05:16:49.892167+00:00
-- url     : https://prove2.me/theorems/f5d6fcd5-53fa-4ff2-900f-f4158309832f
-- title:
--   Ásgeirsson sphere mean for $r > 0$ (non-constant case)
-- statement:
--   Let $u$ be $C^2$ on $\mathbb R^n\times\mathbb R^n$ with $\nabla_x^2 u=\nabla_y^2 u$, and assume $u$ is not constant. Then for every $r\ne 0$ and basepoints $x_0,y_0$, the mean of $u$ over the $x$-sphere of radius $r$ (with $y=y_0$) equals the mean over the $y$-sphere of radius $r$ (with $x=x_0$).
-- source:
--   M. Tegmark, Class. Quantum Grav. 14 (1997) L69–L75; Ásgeirsson mean value theorem (ultrahyperbolic case, $r>0$)

import Mathlib
import Definitions.Def_tegmark_laplacian
open MeasureTheory

namespace TegmarkDimensionality

/-- For `r > 0` and non-constant data, the equality of $x$- and $y$-sphere means is the
full Ásgeirsson theorem (ultrahyperbolic symmetry). -/
theorem asgeirsson_mean_value_positive_radius (n : ℕ)
    (u : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → ℝ) (hu : ContDiff ℝ 2 u)
    (hU : ∀ x y, laplacian (fun x' => u (x', y)) x = laplacian (fun y' => u (x, y')) y)
    (x₀ y₀ : EuclideanSpace ℝ (Fin n)) (r : ℝ) (hr : r ≠ 0)
    (hnc : ¬∀ c, ∀ p, u p = c) :
    ∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1, u (x₀ + r • (ω : EuclideanSpace ℝ (Fin n)), y₀) ∂(volume.toSphere) =
      ∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1, u (x₀, y₀ + r • (ω : EuclideanSpace ℝ (Fin n))) ∂(volume.toSphere) := by sorry

end TegmarkDimensionality
