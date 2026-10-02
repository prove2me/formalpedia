-- Prove2me | Theorems.Thm_TegmarkDimensionality_asgeirsson_mean_value
-- name    : TegmarkDimensionality.asgeirsson_mean_value
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-02T10:07:31.528019+00:00
-- url     : https://prove2.me/theorems/f2cda643-e3e9-4015-9d31-569bcfbc1f28
-- title:
--   Ásgeirsson's mean value theorem for the ultrahyperbolic equation
-- statement:
--   Let $n\ge0$ and let $u(x,y)$ be a $C^2$ function on $\mathbb R^n\times\mathbb R^n$ solving the ultrahyperbolic equation
--   $$\nabla_x^2u(x,y)=\nabla_y^2u(x,y).$$
--   Then for all $x_0,y_0\in\mathbb R^n$ and $r\in\mathbb R$, the mean of $u$ over the sphere of radius $r$ about $x_0$ in the first variable equals its mean over the sphere of radius $r$ about $y_0$ in the second variable:
--   $$\int_{S^{n-1}}u(x_0+r\omega,\,y_0)\,d\sigma(\omega)=\int_{S^{n-1}}u(x_0,\,y_0+r\omega)\,d\sigma(\omega),$$
--   where $\sigma$ is the surface measure on the unit sphere.
--
--   The paper uses this theorem to show that data for hyperbolic equations on non-space-like surfaces, and all data for ultrahyperbolic equations, overdetermine the solution and lead to ill-posed problems.
--
--   **Formalization Note** $\sigma$ is Mathlib's measure on the unit sphere induced from Lebesgue measure (`volume.toSphere`). Both sides use the same normalization, so integrals and means coincide up to the same factor. Global $C^2$ regularity on $\mathbb R^n\times\mathbb R^n$ is assumed.
-- source:
--   M. Tegmark, *On the dimensionality of spacetime*, Class. Quantum Grav. 14 (1997) L69–L75, https://doi.org/10.1088/0264-9381/14/4/002, p. L73, seventh paragraph ('A corollary of a remarkable theorem by Asgeirsson [13] ...') and p. L74 ('Asgeirsson's theorem also applies to the ultrahyperbolic case'); L. Ásgeirsson, Math. Ann. 113 (1936) 321

import Mathlib
import Definitions.Def_tegmark_laplacian
open MeasureTheory

namespace TegmarkDimensionality

/-- Ásgeirsson's mean value theorem: if `u(x, y)` is `C²` on `ℝⁿ × ℝⁿ` and satisfies the
ultrahyperbolic equation `∇ₓ² u = ∇_y² u`, then for all `x₀, y₀` and `r` the mean of `u`
over the sphere of radius `r` about `x₀` in the `x`-variables (with `y = y₀`) equals the mean
over the sphere of radius `r` about `y₀` in the `y`-variables (with `x = x₀`). -/
theorem asgeirsson_mean_value (n : ℕ)
    (u : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → ℝ) (hu : ContDiff ℝ 2 u)
    (hU : ∀ x y, laplacian (fun x' => u (x', y)) x = laplacian (fun y' => u (x, y')) y)
    (x₀ y₀ : EuclideanSpace ℝ (Fin n)) (r : ℝ) :
    ∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1, u (x₀ + r • (ω : EuclideanSpace ℝ (Fin n)), y₀) ∂(volume.toSphere) =
      ∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1, u (x₀, y₀ + r • (ω : EuclideanSpace ℝ (Fin n))) ∂(volume.toSphere) := by sorry

end TegmarkDimensionality
