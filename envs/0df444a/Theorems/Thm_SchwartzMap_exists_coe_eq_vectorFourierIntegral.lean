-- Prove2me | Theorems.Thm_SchwartzMap_exists_coe_eq_vectorFourierIntegral
-- name    : SchwartzMap.exists_coe_eq_vectorFourierIntegral
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.134728+00:00
-- url     : https://prove2.me/theorems/a9d713d7-f2be-5982-a657-fce80ce2363a
-- title:
--   Fourier transform for a nondegenerate pairing preserves S(V)
-- statement:
--   Let $V$ be a finite-dimensional real normed vector space, equipped with its Borel $\sigma$-algebra, let $\mu$ be a measure on $V$ that is an additive Haar measure, let $B : V \times V \to \mathbb{R}$ be a bilinear form on $V$ which is nondegenerate, and let $f$ be a Schwartz function $V \to \mathbb{C}$, i.e. an element of $\mathcal S(V,\mathbb C)$. The assertion is that there exists $g \in \mathcal S(V,\mathbb C)$ whose underlying function is equal to the vector-valued Fourier integral of $f$ taken with respect to the additive character $\mathbf e(x) = e^{2\pi i x}$, the measure $\mu$ and the pairing $B$, that is, to the function
--   $$y \mapsto \int_V \mathbf e(-B(v)(y))\, f(v)\, d\mu(v).$$
--   Thus the conclusion is stated as the existence of a Schwartz-space element coercing to this transform, rather than as a map or a continuous linear operator on $\mathcal S(V,\mathbb C)$; this is the form in which the transform can be substituted into statements quantified over $\mathcal S(V,\mathbb C)$.
--
--   This is the classical stability of the Schwartz space under the Fourier transform, in the generality of an arbitrary Haar measure and an arbitrary nondegenerate bilinear pairing on a finite-dimensional real vector space rather than the Euclidean transform with Lebesgue measure. It is used in the adelic Fourier analysis over a number field, where transforms at the archimedean places must be recognised again as Schwartz functions, in particular for Fourier inversion and for membership in Schwartz–Bruhat spaces.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_SchwartzMap_exists_coe_eq_vectorFourierIntegral.lean

import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Fourier.FourierTransform

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped FourierTransform SchwartzMap

theorem SchwartzMap.exists_coe_eq_vectorFourierIntegral
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    (μ : MeasureTheory.Measure V) [μ.IsAddHaarMeasure]
    (B : LinearMap.BilinForm ℝ V) (hB : B.Nondegenerate) (f : 𝓢(V, ℂ)) :
    ∃ g : 𝓢(V, ℂ), ⇑g = VectorFourier.fourierIntegral 𝐞 μ B f := by sorry
