-- Prove2me | Theorems.Thm_VectorFourier_ae_eq_zero_of_integrable_of_forall_fourierIntegral_eq_zero
-- name    : VectorFourier.ae_eq_zero_of_integrable_of_forall_fourierIntegral_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/8a37f071-304d-50bf-87e8-919805366a9d
-- title:
--   Injectivity of the Fourier transform on integrable functions
-- statement:
--   Let $V$ be a finite-dimensional real normed space carrying its Borel $\sigma$-algebra, let $\mu$ be an additive Haar measure on $V$, and let $B : V \times V \to \mathbb{R}$ be a bilinear form on $V$ which is non-degenerate in the sense of `LinearMap.BilinForm.Nondegenerate`. Let $f : V \to \mathbb{C}$ be integrable with respect to $\mu$, and suppose that its vector-valued Fourier integral with respect to the additive character $\mathbf{e}(t) = e^{2\pi i t}$, the measure $\mu$ and the pairing $B$ vanishes at every point, i.e. $\int_V \mathbf{e}(-B(v,w))\, f(v)\, d\mu(v) = 0$ for all $w \in V$. The conclusion is that $f = 0$ $\mu$-almost everywhere, i.e. $f$ agrees with the zero function outside a $\mu$-null set.
--
--   This is the uniqueness (injectivity) theorem for the Fourier transform on $L^1$, here in the coordinate-free form in which the pairing between the space and its dual is supplied by an arbitrary non-degenerate bilinear form $B$ on $V$ and the measure by an arbitrary additive Haar measure. It is used to produce, for a nonzero continuous integrable function, a frequency at which the corresponding oscillatory integral is nonzero ([`MeasureTheory.exists_integral_fourierChar_bilinForm_mul_ne_zero_of_continuousOn`](thm.html#MeasureTheory.exists_integral_fourierChar_bilinForm_mul_ne_zero_of_continuousOn)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_VectorFourier_ae_eq_zero_of_integrable_of_forall_fourierIntegral_eq_zero.lean

import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Fourier.FourierTransform

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory
open scoped FourierTransform

theorem VectorFourier.ae_eq_zero_of_integrable_of_forall_fourierIntegral_eq_zero
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) [μ.IsAddHaarMeasure]
    (B : LinearMap.BilinForm ℝ V) (_hB : B.Nondegenerate)
    (f : V → ℂ) (_hf : Integrable f μ)
    (_h : ∀ w : V, VectorFourier.fourierIntegral 𝐞 μ B f w = 0) :
    f =ᵐ[μ] 0 := by sorry
