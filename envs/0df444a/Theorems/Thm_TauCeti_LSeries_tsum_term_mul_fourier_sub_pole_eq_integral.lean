-- Prove2me | Theorems.Thm_TauCeti_LSeries_tsum_term_mul_fourier_sub_pole_eq_integral
-- name    : TauCeti.LSeries.tsum_term_mul_fourier_sub_pole_eq_integral
-- status  : Proved
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:07:29.580993+00:00
-- url     : https://prove2.me/theorems/fb01eab0-fa35-4efb-93d2-1a222015edfd
-- title:
--   The pole-subtracted Fourier identity inside the half-plane
-- statement:
--   Let $(a_n)$ be a complex sequence, $A\in\mathbb C$, $x>0$, and $\sigma>1$. Suppose $F(s)=\sum_{n\ge1}a_n n^{-s}$ converges absolutely at the real point $\sigma$, and let $G$ satisfy $G(\sigma+it)=F(\sigma+it)-A/(\sigma+it-1)$ for every $t\in\mathbb R$. For every integrable $\psi:\mathbb R\to\mathbb C$, Use the Fourier convention $\widehat\psi(v)=\int_{\mathbb R}\psi(t)e^{-2\pi itv}\,dt$.
--
--   $$
--   \begin{aligned}
--   &\sum_{n\ge1}\frac{a_n}{n^\sigma}\widehat\psi\!\left(\frac{\log(n/x)}{2\pi}\right)
--   -Ax^{1-\sigma}\int_{-\log x}^\infty e^{-u(\sigma-1)}\widehat\psi\!\left(\frac u{2\pi}\right)\,du\\
--   &\hspace{2em}=\int_{\mathbb R}G(\sigma+it)\psi(t)x^{it}\,dt.
--   \end{aligned}
--   $$
--
--   This isolates the pole-subtracted remainder on a vertical line without requiring boundary continuity.
--
--   Source: the [Tau Ceti contributors](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/LSeries/WienerIkehara/Fourier.lean#L241-L324) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`).
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/LSeries/WienerIkehara/Fourier.lean#L241-L324

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















/-! ### The simple-pole term -/









/-! ### Subtracting the pole -/

theorem TauCeti.LSeries.tsum_term_mul_fourier_sub_pole_eq_integral {G : ℂ → ℂ} {A : ℂ}
    (hG : ∀ t : ℝ, G (sigma + t * _root_.Complex.I) = _root_.LSeries a (sigma + t * _root_.Complex.I) -
      A / (sigma + t * _root_.Complex.I - 1))
    (hpsi : _root_.MeasureTheory.Integrable psi) (hx : 0 < x)
    (hsigma : 1 < sigma) (hsigmaSum : _root_.LSeriesSummable a (sigma : ℂ)) :
    (∑' n : ℕ, _root_.LSeries.term a sigma n *
        _root_.FourierTransform.fourier psi (1 / (2 * π) * _root_.Real.log (n / x))) -
      A * (x ^ (1 - sigma) : ℝ) *
        ∫ u in _root_.Set.Ici (-_root_.Real.log x), _root_.Real.exp (-u * (sigma - 1)) *
          _root_.FourierTransform.fourier psi (u / (2 * π)) =
      ∫ t : ℝ, G (sigma + t * _root_.Complex.I) * psi t * x ^ (t * _root_.Complex.I) := by sorry
