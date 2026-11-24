-- Prove2me | Theorems.Thm_RoughSurfaceScattering_harmonic_gradient_estimate_C_R3
-- name    : RoughSurfaceScattering.harmonic_gradient_estimate_C_R3
-- status  : Proved
-- author  : @もち
-- created : 2026-11-24T10:28:35.360226+00:00
-- url     : https://prove2.me/theorems/a1115d39-0ef6-494f-ac4e-c74196fb6f24
-- title:
--   Gradient estimate $\|Df(z)\|\le\frac Cr\sup_{\overline B(z,r)}|f|$ for harmonic functions on $\mathbb R^3$, with a universal $C$
-- statement:
--   There is a universal constant $C>0$ with the following property. Let $U\subseteq\mathbb R^3$ be open, $f:U\to\mathbb C$ harmonic on $U$, $r>0$ with $\overline B(z,r)\subseteq U$, and $|f|\le K$ on $\overline B(z,r)$. Then
--
--   $$\|Df(z)\|\le\frac Cr\,K .$$
--
--   This is the first-order interior estimate for harmonic functions, in the form needed for Cauchy estimates by nested balls. Unlike `harmonic_gradient_estimate_R3`, the constant is not specified. This allows a proof from the mollifier identity $f=\varphi_\rho*f$ alone, without spherical integrals: differentiating the convolution gives $\|Df(z)\|\le K\,\|D\varphi_\rho\|_{L^1}=K\,\|D\varphi_1\|_{L^1}/\rho$.
--
--   **Formalization Note** $\|Df(z)\|$ is the operator norm of `fderiv ℝ f z`. The constant is quantified before the function, so it is uniform over all harmonic $f$, open sets and radii.
-- source:
--   L. C. Evans, Partial Differential Equations, 2nd ed., §2.2.3, Theorem 7 (estimates on derivatives, case k = 1), here with an unspecified universal constant, obtained from the representation u = η_ρ * u by a radial mollifier (proof of Theorem 6).

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem harmonic_gradient_estimate_C_R3 : ∃ C : ℝ, 0 < C ∧
    ∀ (f : EuclideanSpace ℝ (Fin 3) → ℂ) (U : Set (EuclideanSpace ℝ (Fin 3))),
      IsOpen U → InnerProductSpace.HarmonicOnNhd f U →
      ∀ (z : EuclideanSpace ℝ (Fin 3)) (r : ℝ), 0 < r → Metric.closedBall z r ⊆ U →
      ∀ K : ℝ, (∀ w ∈ Metric.closedBall z r, ‖f w‖ ≤ K) →
        ‖fderiv ℝ f z‖ ≤ C / r * K := by sorry

end RoughSurfaceScattering
