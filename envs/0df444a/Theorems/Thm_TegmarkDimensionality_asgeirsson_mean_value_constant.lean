-- Prove2me | Theorems.Thm_TegmarkDimensionality_asgeirsson_mean_value_constant
-- name    : TegmarkDimensionality.asgeirsson_mean_value_constant
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T05:16:44.873336+00:00
-- url     : https://prove2.me/theorems/96aeb6d5-cfda-41f7-8400-82647b71c234
-- title:
--   Ásgeirsson sphere means for constant fields
-- statement:
--   If $u(x,y)\equiv c$ is constant on $\mathbb R^n\times\mathbb R^n$, then the $x$-sphere mean and $y$-sphere mean about $(x_0,y_0)$ coincide for every radius $r$.
-- source:
--   M. Tegmark, Class. Quantum Grav. 14 (1997) L69–L75; trivial case of Ásgeirsson's mean value theorem

import Mathlib
import Definitions.Def_tegmark_laplacian
open MeasureTheory

namespace TegmarkDimensionality

/-- If `u` is constant, the two sphere means are equal (and equal to that constant). -/
theorem asgeirsson_mean_value_constant (n : ℕ) (c : ℝ)
    (u : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → ℝ) (hu : ContDiff ℝ 2 u)
    (hU : ∀ x y, laplacian (fun x' => u (x', y)) x = laplacian (fun y' => u (x, y')) y)
    (hconst : ∀ p, u p = c)
    (x₀ y₀ : EuclideanSpace ℝ (Fin n)) (r : ℝ) :
    ∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1, u (x₀ + r • (ω : EuclideanSpace ℝ (Fin n)), y₀) ∂(volume.toSphere) =
      ∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1, u (x₀, y₀ + r • (ω : EuclideanSpace ℝ (Fin n))) ∂(volume.toSphere) := by sorry

end TegmarkDimensionality
