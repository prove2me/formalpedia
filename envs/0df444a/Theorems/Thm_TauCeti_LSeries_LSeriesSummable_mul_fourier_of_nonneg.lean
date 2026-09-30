-- Prove2me | Theorems.Thm_TauCeti_LSeries_LSeriesSummable_mul_fourier_of_nonneg
-- name    : TauCeti.LSeries.LSeriesSummable_mul_fourier_of_nonneg
-- status  : Proved
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:13:42.548279+00:00
-- url     : https://prove2.me/theorems/909195eb-ddcf-48f1-b926-182c3125f968
-- title:
--   Boundary summability of a Fourier-weighted Dirichlet series
-- statement:
--   Let $a_n$ be nonnegative real numbers regarded as complex coefficients, and let $A\in\mathbb C$. Suppose $F(\sigma)=\sum_{n\ge1}a_n n^{-\sigma}$ converges absolutely for $1<\sigma\le2$, and $G(\sigma)=F(\sigma)-A/(\sigma-1)$ extends continuously to the real interval $[1,2]$. Use the Fourier convention $\widehat\psi(v)=\int_{\mathbb R}\psi(t)e^{-2\pi itv}\,dt$. For every $\psi\in C_c^\infty(\mathbb R,\mathbb C)$ and every $x>0$,
--
--   $$
--   \sum_{n\ge1}\frac{a_n}{n}\widehat\psi\!\left(\frac{\log(n/x)}{2\pi}\right)\quad\text{converges absolutely}.
--   $$
--
--   This supplies the boundary summability hypothesis for smooth compactly supported tests.
--
--   Source: the [Tau Ceti contributors](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/LSeries/WienerIkehara/BoundaryGrowth.lean#L179-L225) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`).
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/LSeries/WienerIkehara/BoundaryGrowth.lean#L179-L225

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.NumberTheory.LSeries.Deriv

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# A growth bound for nonnegative coefficients, and the summability it supplies

The smoothed Wiener--Ikehara asymptotic
`TauCeti.LSeries.tendsto_tsum_term_mul_fourier_atTop` still carries a summability hypothesis: the
Fourier-weighted series `∑ a n 𝓕 psi (log (n / x) / 2π) / n` has to converge on the boundary line
`Re s = 1`, where the coefficients are no longer damped by `n ^ (-(sigma - 1))`. This file removes
that hypothesis for nonnegative coefficients, which is the only case Wiener--Ikehara is about.

The input is coefficient nonnegativity together with the boundary remainder data on the real
segment `sigma ∈ (1, 2]`; the growth bound for the partial sums is derived from them, not assumed.
Nonnegativity turns the boundary data into the one-sided estimate
`∑ ‖a n‖ / n ^ sigma ≤ B / (sigma - 1)` on `(1, 2]`, and inserting
`sigma = 1 + 1 / log t` into it bounds `∑_{n ≤ t} ‖a n‖` by a multiple of `t log t`. That is weaker
than the Chebyshev bound `O(t)` which Wiener--Ikehara ultimately proves, but it is available before
any Tauberian argument, and one logarithm to spare is all the summability needs: the Fourier
transform of a smooth compactly supported function decays faster than `|v| ^ (-3)`, so the factor
attached to `a n` is `O((log n) ^ (-3))`, and the Abel-summation bound
`TauCeti.LSeries.LSeriesSummable_mul_of_norm_le` converts `O(t log t)` partial sums into a
convergent series.

Only the values of the boundary remainder on the real segment `sigma ∈ (1, 2]` enter the growth
bound, so the results below are stated with the boundary data restricted to that segment; the final
asymptotic specializes the half-plane hypotheses it inherits from
`TauCeti.LSeries.tendsto_tsum_term_mul_fourier_atTop_of_contDiff`.

## Main results

* `TauCeti.LSeries.tsum_norm_term_le_of_boundary`: nonnegative coefficients with a boundary
  remainder continuous on the segment `[1, 2]` have a convergent norm series with
  `∑ ‖term a sigma n‖ ≤ B / (sigma - 1)` on `(1, 2]`.
* `TauCeti.LSeries.isBigO_sum_Icc_norm_of_boundary`: the resulting `O(t log t)` bound for the
  partial sums.
* `TauCeti.LSeries.LSeriesSummable_mul_fourier_of_nonneg`: the Fourier weight is small enough for
  that bound to force summability at `s = 1`, at every scale `x > 0`.
* `TauCeti.LSeries.tendsto_tsum_term_mul_fourier_atTop_of_nonneg`: **the smoothed Wiener--Ikehara
  asymptotic for nonnegative coefficients**, with no summability hypothesis left.

## References

* J. Korevaar, *Tauberian Theory: A Century of Developments*, Chapter III.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter II.
-/

 section

namespace TauCeti.LSeries
end TauCeti.LSeries
section TauCeti.LSeries
open TauCeti TauCeti.LSeries

open Asymptotics Complex Filter FourierTransform MeasureTheory Real Set
open scoped ComplexOrder ContDiff Topology

variable {a : ℕ → ℂ} {A : ℂ} {G : ℂ → ℂ} {psi : ℝ → ℂ} {x : ℝ}

/-! ### The one-sided bound coming from the boundary data -/



/-! ### The partial-sum bound -/



/-! ### The Fourier weight -/

theorem TauCeti.LSeries.LSeriesSummable_mul_fourier_of_nonneg (ha : 0 ≤ a)
    (hG : _root_.ContinuousOn (fun sigma : ℝ ↦ G (sigma : ℂ)) (_root_.Set.Icc 1 2))
    (hG' : ∀ sigma : ℝ, 1 < sigma → sigma ≤ 2 →
      G (sigma : ℂ) = _root_.LSeries a (sigma : ℂ) - A / ((sigma : ℂ) - 1))
    (hsum : ∀ sigma : ℝ, 1 < sigma → sigma ≤ 2 → _root_.LSeriesSummable a (sigma : ℂ))
    (hpsi : _root_.ContDiff ℝ ∞ psi) (hsupp : _root_.HasCompactSupport psi) (hx : 0 < x) :
    _root_.LSeriesSummable (fun n : ℕ ↦ a n * 𝓕 psi (1 / (2 * π) * _root_.Real.log (n / x))) 1 := by sorry
