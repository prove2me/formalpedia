-- Prove2me | Theorems.Thm_TaoFivePrimes_prop72_zero_series_remainder_bound
-- name    : TaoFivePrimes.prop72_zero_series_remainder_bound
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-13T19:09:55.755002+00:00
-- url     : https://prove2.me/theorems/4729135f-73f4-4e70-b231-88c921d8d421
-- title:
--   Proposition 7.2 — quantitative actual-zero remainder estimate
-- statement:
--   Put $T_0=3.29\times10^9$. Let $\eta:\mathbb R\to\mathbb R$ be smooth, nonnegative and supported on $[c,c']$, where $c>0$ and $cx\ge1000$. Suppose
--
--   $$
--   |\alpha|\le\frac{T_0}{4\pi c'x},
--   $$
--
--   and suppose every actual critical-strip zero of $\zeta$ with $0\le\Im\rho\le T_0$ lies on $\Re\rho=1/2$. Write
--
--   $$
--   R=\sum_{\substack{\zeta(\rho)=0\\0<\Re\rho<1}}
--    m(\rho)\int_{\mathbb R}\eta(u/x)e(\alpha u)u^{\rho-1}\,du
--   +\int_{\mathbb R}\frac{\eta(u/x)e(\alpha u)}{u^3-u}\,du.
--   $$
--
--   Then
--
--   $$
--   |R|\le A\frac{\log T_0}{3T_0}x
--   +2.01c^{-1/2}\sqrt{x}\,N(T_0)\|\eta\|_1,
--   \qquad
--   A=60\|\eta\|_1+32c'\|\eta'\|_1+4(c')^2\|\eta''\|_1.
--   $$
--
--   The number $N(T_0)$ counts zeros in the closed strip $0\le\Re\rho\le1$, $0\le\Im\rho\le T_0$, with analytic multiplicity. This is the quantitative zero-series and trivial-zero estimate in the proof of Tao's Proposition 7.2. The full explicit formula converts it into the existing captain milestone `major_arc_sums_positive_scale`. The RH placement clause is an explicit premise of this analytic estimate; the finite verification remains a separate target.
-- source:
--   Terence Tao, arXiv:1201.6656v4, Section 7, proof of Proposition 7.2, the bound following application of (7.1), low-zero contribution, trivial-zero absorption and high-zero integration by parts (7.5) onward, https://arxiv.org/html/1201.6656v4#S7. Exact spectral input for captain positive-scale M23, with analytic multiplicities and finite-height RH placement explicit.

import Mathlib
import Definitions.Def_TaoFivePrimes_SmoothedExpSum
import Definitions.Def_TaoFivePrimes_RepresentationCount
import Definitions.Def_ConnesRZ_weil_defs

open TaoFivePrimes
open MeasureTheory

namespace TaoFivePrimes

theorem prop72_zero_series_remainder_bound (η : ℝ → ℝ) (c c' x α : ℝ)
    (hsmooth : ContDiff ℝ (⊤ : ℕ∞) η)
    (hnonneg : ∀ y, 0 ≤ η y)
    (hsupp : ∀ y, η y ≠ 0 → y ∈ Set.Icc c c')
    (hc : 0 < c)
    (hcx : (10 : ℝ) ^ 3 ≤ c * x)
    (hRH : ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 → 0 ≤ s.im →
      s.im ≤ 3.29 * 10 ^ 9 → s.re = 1 / 2)
    (hα : |α| ≤ 3.29 * 10 ^ 9 / (4 * Real.pi * c' * x)) :
    ‖(∑' rho : {s : ℂ // ConnesRZ.IsCriticalZero s},
        (analyticOrderNatAt riemannZeta rho.val : ℂ) *
          (∫ u : ℝ, (η (u / x) : ℂ) * expCircle (α * u) * (u : ℂ) ^ (rho.val - 1))) +
      (∫ u : ℝ, (η (u / x) : ℂ) * expCircle (α * u) / (((u ^ 3 - u : ℝ) : ℂ)))‖ ≤
      (60 * (∫ y, |η y|) + 32 * c' * (∫ y, |deriv η y|)
          + 4 * c' ^ 2 * (∫ y, |deriv (deriv η) y|))
        * (Real.log (3.29 * 10 ^ 9) / (3 * (3.29 * 10 ^ 9))) * x
      + 2.01 / Real.sqrt c * Real.sqrt x
          * (∑ᶠ s ∈ {s : ℂ | 0 ≤ s.re ∧ s.re ≤ 1 ∧ 0 ≤ s.im ∧ s.im ≤ 3.29 * 10 ^ 9 ∧
                riemannZeta s = 0}, (analyticOrderNatAt riemannZeta s : ℝ))
          * (∫ y, |η y|) := by
  sorry

end TaoFivePrimes
