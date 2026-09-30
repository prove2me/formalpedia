-- Prove2me | Theorems.Thm_TauCeti_LSeries_tendsto_tsum_term_mul_fourier
-- name    : TauCeti.LSeries.tendsto_tsum_term_mul_fourier
-- status  : Proved
-- author  : @riccardo.brasca
-- created : 2026-09-29T20:45:13.496993+00:00
-- url     : https://prove2.me/theorems/01d5d0f6-1252-4f0c-80af-e2cc2554f20c
-- title:
--   Boundary convergence of a Fourier-weighted Dirichlet series
-- statement:
--   Let $(a_n)$ be a complex sequence, $\psi:\mathbb R\to\mathbb C$, and $x\in\mathbb R$. Use the Fourier convention $\widehat\psi(v)=\int_{\mathbb R}\psi(t)e^{-2\pi itv}\,dt$. Put $b_n=a_n\widehat\psi(\log(n/x)/(2\pi))$ for $n\ge1$. If $\sum_{n\ge1}|b_n|/n<\infty$, then
--
--   $$
--   \lim_{\sigma\to1^+}\sum_{n\ge1}\frac{b_n}{n^\sigma}=\sum_{n\ge1}\frac{b_n}{n}.
--   $$
--
--   This gives right-continuity at the boundary for the tested coefficient series.
--
--   **Formalization Note** The statement allows all real $x$. Real division is totalized at zero and the real logarithm is $\log|y|$ for $y\ne0$, with value zero at $y=0$; the Fourier integral is also the totalized integral. No extra integrability assumption on $\psi$ is imposed.
--
--   Source: the [Tau Ceti contributors](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/LSeries/WienerIkehara/Limit.lean#L70-L90) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`).
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/LSeries/WienerIkehara/Limit.lean#L70-L90

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.NumberTheory.LSeries.Deriv

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# The limiting Fourier identity for Wiener--Ikehara

`TauCeti.LSeries.tsum_term_mul_fourier_sub_pole_eq_integral` tests a Dirichlet series against an
integrable function on a vertical line `Re s = sigma` strictly inside the half-plane of
convergence. This file lets `sigma` decrease to `1` and records the resulting identity on the
boundary line itself.

Each of the three terms of that identity has its own limit argument, and each is stated separately
so that a later step can reuse it: the Dirichlet series converges by the uniform convergence of a
summable Dirichlet series on a closed half-plane, while the two integrals converge by dominated
convergence, the pole term because the exponential damping `exp (-u (sigma - 1))` is bounded on
the half-line of integration, and the vertical integral because a test function with compact
support confines the integrand to a compact box on which `G` is continuous.

Only the pole-subtracted remainder `G` is assumed continuous on the closed half-plane
`Re s ≥ 1`; nothing is assumed about `LSeries a` there, where it is a total function with junk
values.

## Main results

* `TauCeti.LSeries.tendsto_tsum_term_mul_fourier` and
  `TauCeti.LSeries.tendsto_integral_vertical` are two of the three one-sided limits; the third,
  for the pole term, is the general `TauCeti.tendsto_integral_exp_mul`.
* `TauCeti.LSeries.tsum_term_mul_fourier_sub_pole_eq_integral_boundary` is the identity they
  combine into, and
  `TauCeti.LSeries.tsum_term_mul_fourier_sub_pole_eq_integral_boundary_of_contDiff` is its form
  for a smooth test function, where the half-line integrability hypothesis is automatic by
  `TauCeti.integrable_fourier_of_contDiff_of_hasCompactSupport`.

## Provenance

The decomposition into three separate one-sided limits, and the shape of the identity they
combine into, follow `limiting_fourier_lim1`, `limiting_fourier_lim2`, `limiting_fourier_lim3`
and `limiting_fourier` in `PrimeNumberTheoremAnd/Wiener.lean` of the Apache-2.0
`AxiomMath/PrimeNumberTheoremAnd` repository, revision
`2667e414c38e5a5dc9aa1946f16f13001e5cd3ed`, the same source as the sibling file
`TauCeti.NumberTheory.LSeries.WienerIkehara.Fourier`. The proofs here are written against
Mathlib's uniform- and dominated-convergence lemmas, and the hypotheses differ: the Chebyshev-type
bound of the source is replaced by the summability of the Fourier-weighted series at `s = 1`,
which is what the limit actually consumes.

## References

* J. Korevaar, *Tauberian Theory: A Century of Developments*, Chapter III.
-/

 section

namespace TauCeti.LSeries
end TauCeti.LSeries
section TauCeti.LSeries
open TauCeti TauCeti.LSeries

open Complex Filter FourierTransform MeasureTheory Real Set
open scoped ContDiff Topology

variable {a : ℕ → ℂ} {psi : ℝ → ℂ} {G : ℂ → ℂ} {A : ℂ} {x : ℝ}

/-! ### The Dirichlet series -/

theorem TauCeti.LSeries.tendsto_tsum_term_mul_fourier (hFsum : _root_.LSeriesSummable
    (fun n : ℕ ↦ a n * 𝓕 psi (1 / (2 * π) * _root_.Real.log (n / x))) 1) :
    _root_.Filter.Tendsto (fun sigma : ℝ ↦ ∑' n : ℕ,
        _root_.LSeries.term a sigma n * 𝓕 psi (1 / (2 * π) * _root_.Real.log (n / x))) (𝓝[>] 1)
      (𝓝 (∑' n : ℕ, _root_.LSeries.term a 1 n * 𝓕 psi (1 / (2 * π) * _root_.Real.log (n / x)))) := by sorry
