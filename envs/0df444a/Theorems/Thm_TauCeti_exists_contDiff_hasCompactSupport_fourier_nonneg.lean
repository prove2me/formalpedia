-- Prove2me | Theorems.Thm_TauCeti_exists_contDiff_hasCompactSupport_fourier_nonneg
-- name    : TauCeti.exists_contDiff_hasCompactSupport_fourier_nonneg
-- status  : Proved
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:07:27.543207+00:00
-- url     : https://prove2.me/theorems/e9ac6828-e030-4575-9582-5b35403f0a48
-- title:
--   A smooth compactly supported function with positive Fourier mass at zero
-- statement:
--   For every finite-dimensional real inner-product space $V$ with its standard additive Haar measure, there is a complex-valued smooth compactly supported function $\psi$ such that
--
--   $$
--   \widehat\psi(\xi)\in[0,\infty)\quad(\xi\in V),\qquad \widehat\psi(0)>0.
--   $$
--
--   This supplies a test function whose Fourier transform is nonnegative and nonzero at the origin.
--
--   Source and proof credit: the Tau Ceti contributors, [original declaration and proof](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/Analysis/Fourier/NonnegTestFunction.lean#L47-L77), Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`; adapted to Lean 4.33.1.
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/Analysis/Fourier/NonnegTestFunction.lean#L47-L77

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.UniformSpace.UniformApproximation

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# A smooth compactly supported function with nonnegative Fourier transform

On a finite-dimensional real inner-product space there is a smooth, compactly supported function
`psi` whose Fourier transform is real and nonnegative everywhere and strictly positive at the
origin. Such a test function turns a limit statement about a Fourier-weighted sum with nonnegative
summands into an upper bound on the summands near the origin of the frequency variable, which is
how Tauberian arguments extract a Chebyshev-type growth bound from smoothed asymptotics.

The function is the autocorrelation `g ⋆ g` of a real bump function `g`. The bump function is even
and real, so its Fourier transform is real
(`TauCeti.fourier_eq_re_of_map_neg_eq_conj`), and the Fourier transform of the convolution is
the square of that real number (`Real.fourier_mul_convolution_eq`). At the origin it is the square
of `∫ g`, which is positive.

## Main results

* `TauCeti.exists_contDiff_hasCompactSupport_fourier_nonneg`: a smooth compactly supported
  function whose Fourier transform is nonnegative everywhere and positive at `0`.
-/

 section

open Complex MeasureTheory
open scoped ComplexOrder ContDiff Convolution FourierTransform

namespace TauCeti
end TauCeti
section TauCeti
open TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem TauCeti.exists_contDiff_hasCompactSupport_fourier_nonneg :
    ∃ psi : V → ℂ, _root_.ContDiff ℝ ∞ psi ∧ _root_.HasCompactSupport psi ∧
      (∀ ξ : V, 0 ≤ 𝓕 psi ξ) ∧ 0 < 𝓕 psi 0 := by sorry
