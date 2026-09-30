-- Prove2me | Theorems.Thm_TauCeti_LSeries_tendsto_tsum_term_mul_fourier_atTop
-- name    : TauCeti.LSeries.tendsto_tsum_term_mul_fourier_atTop
-- status  : Proved
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:13:55.227065+00:00
-- url     : https://prove2.me/theorems/ac2419a6-a506-4f69-a770-b4fe8e4d8496
-- title:
--   The general Fourier-smoothed Wiener–Ikehara limit
-- statement:
--   Let $a_n\in\mathbb C$, $A\in\mathbb C$, and $F(s)=\sum_{n\ge1}a_nn^{-s}$, absolutely convergent on $\operatorname{Re}s>1$. Suppose $G:\mathbb C\to\mathbb C$ is continuous on $\operatorname{Re}s\ge1$ and $G(s)=F(s)-A/(s-1)$ on $\operatorname{Re}s>1$. Use the Fourier convention $\widehat\psi(v)=\int_{\mathbb R}\psi(t)e^{-2\pi itv}\,dt$. Let $\psi:\mathbb R\to\mathbb C$ be integrable, compactly supported and continuous at zero, with integrable Fourier transform. Suppose that for every sufficiently large real $x$ the series
--   $\sum_{n\ge1}(a_n/n)\widehat\psi(\log(n/x)/(2\pi))$ converges absolutely. Then
--
--   $$
--   \lim_{x\to+\infty}\sum_{n\ge1}\frac{a_n}{n}\widehat\psi\!\left(\frac{\log(n/x)}{2\pi}\right)=2\pi A\psi(0).
--   $$
--
--   The coefficients need not be nonnegative, and $A=0$ is allowed.
--
--   This is the smoothed boundary asymptotic under explicit integrability and summability hypotheses.
--
--   Source: the [Tau Ceti contributors](https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/LSeries/WienerIkehara/Asymptotic.lean#L113-L155) (Apache-2.0, commit `948fe4751b1fe528b6d580c522ca5d743d47f185`).
-- source:
--   https://github.com/TauCetiProject/TauCeti/blob/948fe4751b1fe528b6d580c522ca5d743d47f185/TauCeti/NumberTheory/LSeries/WienerIkehara/Asymptotic.lean#L113-L155

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.NumberTheory.LSeries.Deriv

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# The smoothed asymptotic behind Wiener--Ikehara

`TauCeti.LSeries.tsum_term_mul_fourier_sub_pole_eq_integral_boundary_of_contDiff` writes the
difference between a Fourier-weighted Dirichlet series and its pole contribution as an integral
along the line `Re s = 1`, for every scale `x > 0`. That integral carries the oscillating factor
`x ^ (it)`, so the Riemann--Lebesgue lemma makes it vanish as `x → ∞`. This file records the
resulting asymptotic, and then evaluates the pole contribution in the limit.

The pole contribution is `A * ∫ u in Ici (-log x), 𝓕 psi (u / 2π)`. As `x → ∞` the cutoff
`-log x` runs off to `-∞`, so the integral fills up the whole line, where Fourier inversion
evaluates it as `2π * psi 0`. The Fourier-weighted series therefore has the honest limit
`2π * A * psi 0`; the constant `2π` is the Jacobian of the scaling `u ↦ u / 2π` fixed by the
`x ^ (it)` parameterization.

Only the pole-subtracted remainder `G` is assumed continuous on the closed half-plane `Re s ≥ 1`.
Nothing is assumed about `LSeries a` there, where it is a total function with junk values.

## Main results

* `TauCeti.LSeries.tendsto_tsum_term_mul_fourier_sub_pole_atTop`: the Fourier-weighted Dirichlet
  series and its pole contribution differ by `o(1)` as the scale `x` tends to infinity.
* `TauCeti.LSeries.tendsto_tsum_term_mul_fourier_atTop`: the Fourier-weighted Dirichlet series
  itself tends to `2π * A * psi 0`.

Both are stated for an integrable, compactly supported test function, with the analytic
hypotheses that the two limit arguments actually consume: half-line integrability of `𝓕 psi` for
the first, and integrability of `𝓕 psi` together with continuity of `psi` at `0` for the Fourier
inversion in the second. The hypotheses that vary with the scale `x` are asked for only
eventually as `x → ∞`, which is all an `atTop` limit consumes. The suffixed `..._of_contDiff`
forms specialize both to a smooth test function, for which all of those are automatic.

## Provenance

The statement obtained by letting `x → ∞` in the boundary Fourier identity follows `limiting_cor`
in `PrimeNumberTheoremAnd/Wiener.lean` of the Apache-2.0 `AxiomMath/PrimeNumberTheoremAnd`
repository, revision `2667e414c38e5a5dc9aa1946f16f13001e5cd3ed`, the same source as the sibling
files `TauCeti.NumberTheory.LSeries.WienerIkehara.Fourier` and
`TauCeti.NumberTheory.LSeries.WienerIkehara.Limit`. The evaluation of the limiting pole
contribution by Fourier inversion is not in that source, which keeps the truncated integral.

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

variable {a : ℕ → ℂ} {psi : ℝ → ℂ} {G : ℂ → ℂ} {A : ℂ}

theorem TauCeti.LSeries.tendsto_tsum_term_mul_fourier_atTop
    (hG : _root_.ContinuousOn G {z : ℂ | 1 ≤ z.re})
    (hG' : ∀ z : ℂ, 1 < z.re → G z = _root_.LSeries a z - A / (z - 1))
    (hsum : ∀ sigma : ℝ, 1 < sigma → _root_.LSeriesSummable a sigma)
    (hpsi : _root_.MeasureTheory.Integrable psi) (hsupp : _root_.HasCompactSupport psi) (hF : _root_.MeasureTheory.Integrable (𝓕 psi))
    (hpsi0 : _root_.ContinuousAt psi 0)
    (hFsum : ∀ᶠ x : ℝ in _root_.Filter.atTop, _root_.LSeriesSummable
      (fun n : ℕ ↦ a n * 𝓕 psi (1 / (2 * π) * _root_.Real.log (n / x))) 1) :
    _root_.Filter.Tendsto (fun x : ℝ ↦
        ∑' n : ℕ, _root_.LSeries.term a 1 n * 𝓕 psi (1 / (2 * π) * _root_.Real.log (n / x)))
      _root_.Filter.atTop (𝓝 (2 * (π : ℂ) * A * psi 0)) := by sorry
