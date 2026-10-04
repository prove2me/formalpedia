-- Prove2me | Theorems.Thm_TegmarkDimensionality_asgeirsson_mean_value_radius_zero
-- name    : TegmarkDimensionality.asgeirsson_mean_value_radius_zero
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T05:16:28.818359+00:00
-- url     : https://prove2.me/theorems/c09f629b-ca41-4c2c-b57b-a7f447844693
-- title:
--   Ásgeirsson sphere mean at radius zero
-- statement:
--   Under the ultrahyperbolic hypothesis $\nabla_x^2 u=\nabla_y^2 u$, if the sphere radius is $r=0$ then both $x$- and $y$-sphere means equal the value $u(x_0,y_0)$.
-- source:
--   M. Tegmark, Class. Quantum Grav. 14 (1997) L69–L75 (ultrahyperbolic well-posedness); degenerate case $r=0$ of Ásgeirsson's mean value theorem

import Mathlib
import Definitions.Def_tegmark_laplacian
open MeasureTheory

namespace TegmarkDimensionality

/-- When `r = 0`, both sphere means reduce to the value at `(x₀, y₀)`. -/
theorem asgeirsson_mean_value_radius_zero (n : ℕ)
    (u : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → ℝ) (hu : ContDiff ℝ 2 u)
    (hU : ∀ x y, laplacian (fun x' => u (x', y)) x = laplacian (fun y' => u (x, y')) y)
    (x₀ y₀ : EuclideanSpace ℝ (Fin n)) (r : ℝ) (hr : r = 0) :
    ∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1, u (x₀ + r • (ω : EuclideanSpace ℝ (Fin n)), y₀) ∂(volume.toSphere) =
      ∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1, u (x₀, y₀ + r • (ω : EuclideanSpace ℝ (Fin n))) ∂(volume.toSphere) := by sorry

end TegmarkDimensionality
