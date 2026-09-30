-- Prove2me | Theorems.Thm_TauCeti_LSeries_tsum_term_mul_fourier_eq_integral
-- name    : TauCeti.LSeries.tsum_term_mul_fourier_eq_integral
-- status  : Proved
-- author  : @riccardo.brasca
-- created : 2026-09-29T20:46:14.868584+00:00
-- url     : https://prove2.me/theorems/fc90ad7b-a607-4997-b068-d1c473d62a2f
-- title:
--   Fourier testing of an absolutely convergent Dirichlet series
-- statement:
--   Let $(a_n)$ be a complex sequence and let $\sigma\in\mathbb R$ satisfy $\sum_{n\ge1}|a_n|n^{-\sigma}<\infty$. Set $F(s)=\sum_{n\ge1}a_n n^{-s}$. Let $\psi:\mathbb R\to\mathbb C$ be integrable and let $x>0$. Use the Fourier convention $\widehat\psi(v)=\int_{\mathbb R}\psi(t)e^{-2\pi itv}\,dt$. Then
--
--   $$
--   \sum_{n\ge1}\frac{a_n}{n^\sigma}\widehat\psi\!\left(\frac{\log(n/x)}{2\pi}\right)
--   =\int_{\mathbb R}F(\sigma+it)\psi(t)x^{it}\,dt.
--   $$
--
--   This relates logarithmically weighted coefficient sums to the values of a Dirichlet series on a vertical line.
--
--   Source: the [Tau Ceti contributors](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/LSeries/WienerIkehara/Fourier.lean) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`).
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/LSeries/WienerIkehara/Fourier.lean

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_LSeries_WienerIkehara_Fourier
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.NumberTheory.LSeries.Deriv

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Fourier identities for Wiener--Ikehara

The Fourier proof of Wiener--Ikehara starts by testing a Dirichlet series against an integrable
function on a vertical line. This file records the two exact identities used in that step. The
first exchanges the Dirichlet series with the integral. The second computes the contribution of
the simple pole at `s = 1`. Their combination expresses the difference as the integral of the
pole-subtracted remainder, a function agreeing with `LSeries a - A / (s - 1)` on the open
vertical line `Re s = sigma`; nothing about its boundary behaviour is asserted or used here.

## Main results

* `TauCeti.LSeries.tsum_term_mul_fourier_eq_integral` is the Fourier identity for a
  convergent Dirichlet series.
* `TauCeti.LSeries.integral_exp_mul_fourier_eq` computes the pole term.
* `TauCeti.LSeries.tsum_term_mul_fourier_sub_pole_eq_integral` combines the two when a named
  function agrees with the pole-subtracted remainder on the vertical line.

## Provenance

The proofs are adapted from `PrimeNumberTheoremAnd/Wiener.lean` in the Apache-2.0
`AxiomMath/PrimeNumberTheoremAnd` repository, revision
`2667e414c38e5a5dc9aa1946f16f13001e5cd3ed`. The source declarations are `first_fourier`,
`second_fourier`, and `limiting_fourier_aux`. The statements here use Mathlib's
`LSeriesSummable` directly, remove the source project's local `nterm` wrapper, and rely on
Mathlib's APIs together with the local vertical-line continuity theorem
`TauCeti.LSeries.continuous_LSeries_vertical`.

## References

* J. Korevaar, *Tauberian Theory: A Century of Developments*, Chapter III.
-/

 section

namespace TauCeti.LSeries
end TauCeti.LSeries
section TauCeti.LSeries
open TauCeti TauCeti.LSeries

open Complex Filter FourierTransform MeasureTheory Real Set
open scoped ComplexConjugate Real Topology

variable {a : ℕ → ℂ} {psi : ℝ → ℂ} {x sigma t : ℝ}

theorem TauCeti.LSeries.tsum_term_mul_fourier_eq_integral (hpsi : _root_.MeasureTheory.Integrable psi) (hx : 0 < x)
    (hsigma : _root_.LSeriesSummable a (sigma : ℂ)) :
    ∑' n : ℕ, _root_.LSeries.term a sigma n *
        _root_.FourierTransform.fourier psi (1 / (2 * π) * _root_.Real.log (n / x)) =
      ∫ t : ℝ, _root_.LSeries a (sigma + t * _root_.Complex.I) * psi t * x ^ (t * _root_.Complex.I) := by sorry
