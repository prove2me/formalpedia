-- Prove2me | Theorems.Thm_RoughSurfaceScattering_harmonic_radial_mollifier_R3
-- name    : RoughSurfaceScattering.harmonic_radial_mollifier_R3
-- status  : Open
-- author  : @もち
-- created : 2026-11-24T09:58:35.083383+00:00
-- url     : https://prove2.me/theorems/c34b2ba1-d424-4321-b369-9185e9174a06
-- title:
--   Harmonic functions are invariant under convolution with radial kernels of mass one
-- statement:
--   Let $U\subseteq\mathbb R^3$ be open and $f:U\to\mathbb C$ harmonic on $U$. Let $\varphi:\mathbb R^3\to\mathbb R$ be integrable and radial ($\varphi(y)$ depends only on $|y|$), with
--
--   $$\int_{\mathbb R^3}\varphi=1,\qquad\operatorname{supp}\varphi\subseteq B(0,r),$$
--
--   and let $z$ satisfy $\overline B(z,r)\subseteq U$. Then
--
--   $$f(z)=\int_{\mathbb R^3}\varphi(y)\,f(z-y)\,dy .$$
--
--   By the spherical mean-value property, the average of $f$ over each sphere $\partial B(z,\rho)$ with $\rho<r$ equals $f(z)$. Integrating in polar coordinates against the radial weight $\varphi$ therefore gives $f(z)\int\varphi=f(z)$. This identity shows that harmonic functions coincide locally with their convolutions by smooth radial kernels, and are therefore $C^\infty$ (Weyl's lemma).
--
--   **Formalization Note** Harmonicity is `InnerProductSpace.HarmonicOnNhd`. The kernel need not be nonnegative. Radiality is stated as $|y|=|y'|\Rightarrow\varphi(y)=\varphi(y')$. Mathlib's `ContDiffBump` is not used because its base function is chosen noncomputably and need not be radial.
-- source:
--   L. C. Evans, Partial Differential Equations, 2nd ed., §2.2.2 (mean-value formulas, Theorem 2) and §2.2.3, proof of Theorem 6: for radial mollifiers η_ε, u^ε = η_ε * u equals u, by integrating the spherical mean-value property in polar coordinates.

import Mathlib
import Definitions.Def_RoughSurfaceScattering_Basic

open MeasureTheory

namespace RoughSurfaceScattering

theorem harmonic_radial_mollifier_R3 (f : EuclideanSpace ℝ (Fin 3) → ℂ)
    (U : Set (EuclideanSpace ℝ (Fin 3))) (hU : IsOpen U)
    (hf : InnerProductSpace.HarmonicOnNhd f U) (φ : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hrad : ∀ y y' : EuclideanSpace ℝ (Fin 3), ‖y‖ = ‖y'‖ → φ y = φ y')
    (hφint : Integrable φ) (hφ1 : ∫ y, φ y = 1) (r : ℝ) (hr : 0 < r)
    (hsupp : Function.support φ ⊆ Metric.ball 0 r) (z : EuclideanSpace ℝ (Fin 3))
    (hz : Metric.closedBall z r ⊆ U) :
    f z = ∫ y, φ y • f (z - y) := by sorry

end RoughSurfaceScattering
