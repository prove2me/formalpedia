-- Prove2me | Theorems.Thm_TauCeti_LSeries_tendsto_inv_mul_tsum_mul_div_atTop
-- name    : TauCeti.LSeries.tendsto_inv_mul_tsum_mul_div_atTop
-- status  : Proved
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:14:10.471572+00:00
-- url     : https://prove2.me/theorems/578e57d1-abdb-4614-8cc2-8fa14b5fee24
-- title:
--   A Wiener–Ikehara limit with a smooth positive-axis cutoff
-- statement:
--   Let $a_n\in\mathbb C$, $A\in\mathbb C$, and $F(s)=\sum_{n\ge1}a_nn^{-s}$, absolutely convergent on $\operatorname{Re}s>1$. Suppose $G:\mathbb C\to\mathbb C$ is continuous on $\operatorname{Re}s\ge1$ and $G(s)=F(s)-A/(s-1)$ on $\operatorname{Re}s>1$. Assume also that every $a_n$ is real and nonnegative. Let $\Psi:\mathbb R\to\mathbb C$ be smooth, with compact support contained in $(0,\infty)$. Then
--
--   $$
--   \lim_{x\to+\infty}\frac1x\sum_{n\ge0}a_n\Psi(n/x)
--   =A\int_0^\infty\Psi(y)\,dy.
--   $$
--
--   This provides multiplicatively rescaled smooth cutoff asymptotics for nonnegative Dirichlet coefficients.
--
--   Source: the [Tau Ceti contributors](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/LSeries/WienerIkehara/SharpCutoff.lean#L122-L149) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`).
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/LSeries/WienerIkehara/SharpCutoff.lean#L122-L149

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_LSeries_WienerIkehara_SharpCutoff
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Interval.Finset.SuccPred
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Tactic.FieldSimp
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
# The Wiener--Ikehara theorem

Let `a n ≥ 0` have Dirichlet series `F s = ∑ a n n⁻ˢ` convergent on `Re s > 1`, and suppose that
`F s - κ / (s - 1)` agrees on `Re s > 1` with a function `G` continuous on `Re s ≥ 1`. The
Wiener--Ikehara theorem says that the partial sums then grow like `κ x`:
`x⁻¹ ∑_{1 ≤ n ≤ x} a n → κ` as `x → ∞`.

The analytic input is the smoothed asymptotic
`TauCeti.LSeries.tendsto_tsum_term_mul_fourier_schwartz_atTop`, which evaluates the limit of
`∑ a n / n * 𝓕 g (log (n / x) / 2π)` for a Schwartz function `g`. This file makes two passes.

* **Smooth cutoffs.** For a smooth function `Ψ` with compact support inside `(0, ∞)`, the weight
  `W v = e^{2πv} Ψ(e^{2πv})` is smooth and compactly supported, hence the Fourier transform of the
  Schwartz function `g = 𝓕⁻ W`, and `a n / n * W (log (n / x) / 2π) = x⁻¹ a n Ψ (n / x)`. Since
  `g 0 = ∫ W = (2π)⁻¹ ∫_{(0, ∞)} Ψ`, this gives `x⁻¹ ∑ a n Ψ (n / x) → A ∫_{(0, ∞)} Ψ`.
* **The sharp cutoff.** The indicator of `(0, 1]` is squeezed between two bump functions. The lower
  bump is supported in `(0, 1)`; the upper bump equals `1` on `[ε, 1]`, and the coefficients with
  `n ≤ ε x` that it misses are controlled by the Chebyshev bound
  `TauCeti.LSeries.isBigO_sum_Icc_norm_id_of_boundary`. Letting `ε → 0` gives the theorem.

The coefficients are real and nonnegative, the hypothesis on the series is `LSeriesHasSum` on the
open half-plane (Mathlib's `LSeries` is a total function, zero where the series diverges), and the
continuous extension is a separately named function `G`, so no junk value of `F` at `s = 1` or on
the line `Re s = 1` is ever used. The sign of `κ` is not assumed: it is forced by the conclusion.

## Main results

* `TauCeti.LSeries.tendsto_inv_mul_tsum_mul_div_atTop`: the smoothed asymptotic
  `x⁻¹ ∑ a n Ψ (n / x) → A ∫_{(0, ∞)} Ψ` for a smooth `Ψ` with compact support in `(0, ∞)`.
* `TauCeti.LSeries.wienerIkehara`: **the Wiener--Ikehara theorem**,
  `x⁻¹ ∑_{1 ≤ n ≤ x} a n → κ`.
* `TauCeti.LSeries.wienerIkehara_zero`: the case `κ = 0`, in which `F` itself extends continuously
  to `Re s ≥ 1` and the partial sums are `o(x)`.

## Provenance

The passage from Schwartz test functions to smooth cutoffs on `(0, ∞)` and then to the sharp
cutoff follows `WienerIkeharaSmooth`, `WienerIkeharaInterval` and `WienerIkeharaTheorem'` in
`PrimeNumberTheoremAnd/Wiener.lean` of the Apache-2.0 `AxiomMath/PrimeNumberTheoremAnd`
repository, revision `2667e414c38e5a5dc9aa1946f16f13001e5cd3ed`, the same source as the sibling
files in this directory. Here the smooth step is derived from the Schwartz-function asymptotic
by Fourier inversion on `𝓢(ℝ, ℂ)`, and the sharp step squeezes directly between two
`ContDiffBump`s, spending the Chebyshev bound only on the initial segment `n ≤ ε x`.

## References

* J. Korevaar, *Tauberian Theory: A Century of Developments*, Chapter III.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter II.
-/

 section

open Complex Filter FourierTransform MeasureTheory Real Set
open scoped ComplexOrder ContDiff SchwartzMap Topology

namespace TauCeti.LSeries
end TauCeti.LSeries
section TauCeti.LSeries
open TauCeti TauCeti.LSeries

/-! ### Smooth cutoffs on the positive half-line -/

section Smooth

variable {Ψ : ℝ → ℂ}











variable {a : ℕ → ℂ} {A : ℂ} {G : ℂ → ℂ}

theorem TauCeti.LSeries.tendsto_inv_mul_tsum_mul_div_atTop (ha : 0 ≤ a)
    (hG : _root_.ContinuousOn G {z : ℂ | 1 ≤ z.re})
    (hG' : ∀ z : ℂ, 1 < z.re → G z = _root_.LSeries a z - A / (z - 1))
    (hsum : ∀ sigma : ℝ, 1 < sigma → _root_.LSeriesSummable a sigma)
    (hΨ : _root_.ContDiff ℝ ∞ Ψ) (hΨc : _root_.HasCompactSupport Ψ) (hΨpos : _root_.tsupport Ψ ⊆ _root_.Set.Ioi 0) :
    _root_.Filter.Tendsto (fun x : ℝ ↦ (x : ℂ)⁻¹ * ∑' n : ℕ, a n * Ψ (n / x)) _root_.Filter.atTop
      (𝓝 (A * ∫ y in _root_.Set.Ioi 0, Ψ y)) := by sorry
