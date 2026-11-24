-- Prove2me | Theorems.Thm_RoughSurfaceScattering_harmonic_mean_value_smooth_kernel_R3
-- name    : RoughSurfaceScattering.harmonic_mean_value_smooth_kernel_R3
-- status  : Open
-- author  : @もち
-- created : 2026-11-24T11:08:33.183846+00:00
-- url     : https://prove2.me/theorems/22a6cedc-124b-4e4b-b1ed-5c752dffcac7
-- title:
--   Mean-value property: harmonic functions are invariant under convolution with kernels $h(|y|^2)$ of mass one
-- statement:
--   Let $U\subseteq\mathbb R^3$ be open and $f:U\to\mathbb C$ harmonic on $U$. Let $h:\mathbb R\to\mathbb R$ be continuous with $h(v)=0$ for $v\ge r^2$ (where $r>0$), and
--
--   $$\int_{\mathbb R^3}h(|y|^2)\,dy=1 .$$
--
--   If $\overline B(z,r)\subseteq U$, then
--
--   $$f(z)=\int_{\mathbb R^3}h(|y|^2)\,f(z-y)\,dy .$$
--
--   This is the mean-value property of harmonic functions in convolution form, for radial kernels of the form $h(|y|^2)$. It shows that harmonic functions coincide locally with their convolutions by smooth radial mollifiers, which gives their smoothness and interior derivative estimates.
--
--   **Formalization Note** Harmonicity is `InnerProductSpace.HarmonicOnNhd`. Restricting to kernels $h(|y|^2)$ with continuous $h$ makes $\Psi(y)=\tfrac12\int_{r^2}^{|y|^2}h$ a $C^1$ potential with $\nabla\Psi(y)=h(|y|^2)\,y$, which allows a proof without spherical measure.
-- source:
--   L. C. Evans, Partial Differential Equations, 2nd ed., §2.2.2, Theorem 2 (mean-value formulas), in mollifier form as used in §2.2.3, proof of Theorem 6; proved here by a dilation argument and integration by parts on ℝ³ instead of spherical means.

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem harmonic_mean_value_smooth_kernel_R3 (f : EuclideanSpace ℝ (Fin 3) → ℂ)
    (U : Set (EuclideanSpace ℝ (Fin 3))) (hU : IsOpen U)
    (hf : InnerProductSpace.HarmonicOnNhd f U) (h : ℝ → ℝ) (hh : Continuous h)
    (r : ℝ) (hr : 0 < r) (hsupp : ∀ v : ℝ, r ^ 2 ≤ v → h v = 0)
    (hint : ∫ y : EuclideanSpace ℝ (Fin 3), h (‖y‖ ^ 2) = 1)
    (z : EuclideanSpace ℝ (Fin 3)) (hz : Metric.closedBall z r ⊆ U) :
    f z = ∫ y, h (‖y‖ ^ 2) • f (z - y) := by sorry

end RoughSurfaceScattering
