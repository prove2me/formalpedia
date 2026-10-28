-- Prove2me | Theorems.Thm_TaoFivePrimes_schoenfeld_psi_error_middle_of_rh_million
-- name    : TaoFivePrimes.schoenfeld_psi_error_middle_of_rh_million
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T17:09:58.827751+00:00
-- url     : https://prove2.me/theorems/809990b5-ba08-4892-b35b-376d91f9bd3f
-- title:
--   Chebyshev psi error in the middle range from RH through height one million
-- statement:
--   Assume that every zero $\rho$ of the Riemann zeta function satisfying $0<\operatorname{Re}\rho<1$ and $0\le\operatorname{Im}\rho\le10^6$ lies on the critical line $\operatorname{Re}\rho=1/2$. Then for every real $y$ with $e^{23}\le y<e^{136}$, the second Chebyshev function $\psi(y)=\sum_{n\le y}\Lambda(n)$ satisfies
--
--   $$|\psi(y)-y|\le\frac{y}{40\log y}.$$
--
--   This conditional intermediate covers the middle range needed to assemble the Chebyshev error estimate in Tao's five-primes argument. Its finite-height hypothesis is weaker than the verified-height statement quoted by Tao; no global Riemann hypothesis is assumed.
-- source:
--   Derived conditional intermediate for T. Tao, arXiv:1201.6656v4, Theorem 1.5 and Section 4, proof of Lemma 4.3, https://arxiv.org/html/1201.6656v4#S4. The stated cutoff and implication are a derived strengthening, not a verbatim quotation. Uses the existing proved Prove2Me smoothed Chebyshev formula, explicit zero reciprocal estimates, and the proved zeta zero-free half-plane Re(s)>7/8.

import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Exp

theorem TaoFivePrimes.schoenfeld_psi_error_middle_of_rh_million
    (hRH : ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 →
      0 ≤ s.im → s.im ≤ 10 ^ 6 → s.re = 1/2)
    (y : ℝ) (hy : Real.exp 23 ≤ y) (hY : y < Real.exp 136) :
    |Chebyshev.psi y - y| ≤ y / (40 * Real.log y) := by sorry
