-- Prove2me | Theorems.Thm_TauCeti_LSeries_tendsto_tsum_term_mul_atTop_of_approx_fourier
-- name    : TauCeti.LSeries.tendsto_tsum_term_mul_atTop_of_approx_fourier
-- status  : Proved
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:14:10.400456+00:00
-- url     : https://prove2.me/theorems/e4ba9597-a698-4257-8f59-34042ae58e52
-- title:
--   A smoothed Wiener–Ikehara limit for approximable weights
-- statement:
--   Let $a_n\in\mathbb C$, $A\in\mathbb C$, and $F(s)=\sum_{n\ge1}a_nn^{-s}$, absolutely convergent on $\operatorname{Re}s>1$. Suppose $G:\mathbb C\to\mathbb C$ is continuous on $\operatorname{Re}s\ge1$ and $G(s)=F(s)-A/(s-1)$ on $\operatorname{Re}s>1$. Assume also that every $a_n$ is real and nonnegative. Use the Fourier convention $\widehat\psi(v)=\int_{\mathbb R}\psi(t)e^{-2\pi itv}\,dt$. Let $W:\mathbb R\to\mathbb C$ and $L\in\mathbb C$. Suppose that for every $\varepsilon>0$ there is $\psi\in C_c^\infty(\mathbb R,\mathbb C)$ such that
--
--   $$
--   |W(v)-\widehat\psi(v)|\le\frac\varepsilon{1+v^2}\quad(v\in\mathbb R),\qquad |L-\psi(0)|\le\varepsilon.
--   $$
--
--   Then
--
--   $$
--   \lim_{x\to+\infty}\sum_{n\ge1}\frac{a_n}{n}W\!\left(\frac{\log(n/x)}{2\pi}\right)=2\pi AL.
--   $$
--
--   This extends the smoothed Tauberian limit to weights approximable in a weighted uniform norm.
--
--   Source: the [Tau Ceti contributors](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/LSeries/WienerIkehara/Approximation.lean#L298-L381) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`).
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/LSeries/WienerIkehara/Approximation.lean#L298-L381

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_LSeries_WienerIkehara_Approximation
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
# Approximating the test function in the smoothed Wiener--Ikehara asymptotic

`TauCeti.LSeries.tendsto_tsum_term_mul_fourier_atTop_of_nonneg` evaluates the limit of
`∑ a n / n * 𝓕 psi (log (n / x) / 2π)` for a *smooth compactly supported* test function `psi`.
The Tauberian step of Wiener--Ikehara needs the same limit for weights `W` that are not of this
form. A nonzero smooth compactly supported weight `W` is one: it is the Fourier transform of a
Schwartz function, but never of a compactly supported one, since a nonzero function and its
Fourier transform cannot both have compact support. This file passes the limit from `𝓕 psi` to
any weight `W` that such transforms approximate in the weighted sup norm
`sup_v (1 + v ^ 2) ‖W v - 𝓕 psi v‖`.

The approximation step rests on a uniform bound. If the partial sums of `‖a‖` satisfy the
Chebyshev bound `∑_{1 ≤ n ≤ N} ‖a n‖ ≤ C N`, then
`∑ ‖a n‖ / n * (1 + (log (n / x) / 2π) ^ 2)⁻¹ ≤ C (1 + 2π²)` for every scale `x > 0`.
The weight `t ↦ (t (1 + (log (t / x) / 2π) ^ 2))⁻¹` is antitone on `t > 0`, so Abel's inequality
`TauCeti.sum_range_mul_le_sum_range_mul` bounds the weighted sum by `C` times the sum of the
weight, and the integral test bounds the latter by `1 + ∫ = 1 + 2π (arctan - arctan) ≤ 1 + 2π²`.
Consequently a weight `W` with `‖W v‖ ≤ M (1 + v ^ 2)⁻¹` gives a series of size at most
`M C (1 + 2π²)`, uniformly in `x`, and a small error in the weighted sup norm costs little in the
limit. For nonnegative coefficients with Wiener--Ikehara boundary data the Chebyshev bound is
`TauCeti.LSeries.isBigO_sum_Icc_norm_id_of_boundary`.

## Main results

* `TauCeti.LSeries.tsum_norm_term_mul_inv_one_add_sq_le`: the uniform bound on the
  logarithmically weighted series, from a Chebyshev bound.
* `TauCeti.LSeries.LSeriesSummable_mul_comp_log_div` and
  `TauCeti.LSeries.norm_tsum_term_mul_comp_log_div_le`: summability and the uniform bound for a
  weight `W` with `‖W v‖ ≤ M (1 + v ^ 2)⁻¹`.
* `TauCeti.LSeries.tendsto_tsum_term_mul_atTop_of_approx_fourier`: the smoothed Wiener--Ikehara
  asymptotic for a weight `W` approximable by Fourier transforms of smooth compactly supported
  functions `psi` whose values `psi 0` approximate `L`; the limit is `2π A L`.

## Provenance

The uniform bound and the truncation argument follow `bound_sum_log`, `bound_I1` and
`limiting_cor_W21` in `PrimeNumberTheoremAnd/Wiener.lean` of the Apache-2.0
`AxiomMath/PrimeNumberTheoremAnd` repository, revision
`2667e414c38e5a5dc9aa1946f16f13001e5cd3ed`, the same source as the sibling files in this
directory. Here the summation by parts is the general `TauCeti.sum_range_mul_le_sum_range_mul`,
the integral of the weight is bounded on finite intervals by the fundamental theorem of calculus
rather than evaluated on `(0, ∞)`, and the approximation hypothesis is stated for an arbitrary
weight `W` instead of a fixed truncation of a `W^{2,1}` function. For a Schwartz function `g`
(`limiting_cor_schwartz` there) the approximants are the truncations `χ (R⁻¹ • ·) • g`, which
converge to `g` in the Schwartz topology (`SchwartzMap.tendsto_smulLeftCLM_comp_inv_smul_atTop`);
the weighted sup norm of a Fourier transform is bounded by two Schwartz seminorms, so it is the
continuity of the Fourier transform on `𝓢(ℝ, ℂ)` that makes the truncation error small.

## References

* J. Korevaar, *Tauberian Theory: A Century of Developments*, Chapter III.
-/

 section

namespace TauCeti.LSeries
end TauCeti.LSeries
section TauCeti.LSeries
open TauCeti TauCeti.LSeries

open Complex Filter FourierTransform Real Set
open scoped ComplexOrder ContDiff SchwartzMap Topology

variable {a : ℕ → ℂ} {C x : ℝ}

/-! ### The logarithmic weight -/





















/-! ### The uniform bound -/











/-! ### Weights with quadratic decay -/

variable {W : ℝ → ℂ} {M : ℝ}









/-! ### Passing the smoothed asymptotic to approximable weights -/

variable {G : ℂ → ℂ} {A L : ℂ}

theorem TauCeti.LSeries.tendsto_tsum_term_mul_atTop_of_approx_fourier (ha : 0 ≤ a)
    (hG : _root_.ContinuousOn G {z : ℂ | 1 ≤ z.re})
    (hG' : ∀ z : ℂ, 1 < z.re → G z = _root_.LSeries a z - A / (z - 1))
    (hsum : ∀ sigma : ℝ, 1 < sigma → _root_.LSeriesSummable a sigma)
    (happrox : ∀ ε > 0, ∃ psi : ℝ → ℂ, _root_.ContDiff ℝ ∞ psi ∧ _root_.HasCompactSupport psi ∧
      (∀ v, ‖W v - 𝓕 psi v‖ ≤ ε * (1 + v ^ 2)⁻¹) ∧ ‖L - psi 0‖ ≤ ε) :
    _root_.Filter.Tendsto (fun x : ℝ ↦
        ∑' n : ℕ, _root_.LSeries.term a 1 n * W (1 / (2 * π) * _root_.Real.log (n / x)))
      _root_.Filter.atTop (𝓝 (2 * (π : ℂ) * A * L)) := by sorry
