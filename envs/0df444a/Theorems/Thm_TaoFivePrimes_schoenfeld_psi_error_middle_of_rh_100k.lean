-- Prove2me | Theorems.Thm_TaoFivePrimes_schoenfeld_psi_error_middle_of_rh_100k
-- name    : TaoFivePrimes.schoenfeld_psi_error_middle_of_rh_100k
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T17:16:51.427635+00:00
-- url     : https://prove2.me/theorems/1e87c97b-aaab-4e70-aa2a-59910ade070e
-- title:
--   Middle-range Chebyshev estimate from zeros through height 100,000
-- statement:
--   Let $\psi(y)=\sum_{p^k\le y}\log p$ be Chebyshev's second function. Suppose every zero $\rho$ of the Riemann zeta function with $0<\operatorname{Re}\rho<1$ and $0\le\operatorname{Im}\rho\le 10^5$ lies on the critical line. Then, for every real $y$ with $e^{23}\le y<e^{136}$,
--
--   $$
--   |\psi(y)-y|\le \frac{y}{40\log y}.
--   $$
--
--   This conditional intermediate isolates a finite-height zero-verification input for the explicit Chebyshev estimate used in the five-primes argument.
-- source:
--   Derived conditional intermediate for T. Tao, arXiv:1201.6656v4, Theorem 1.5 and Section 4, proof of Lemma 4.3, https://arxiv.org/html/1201.6656v4#S4. The cutoff and implication are a derived strengthening, not a verbatim quotation. Uses the existing proved Prove2Me smoothed Chebyshev formula, zero reciprocal estimates, and zeta zero-free half-plane Re(s)>7/8.

import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Exp

theorem TaoFivePrimes.schoenfeld_psi_error_middle_of_rh_100k
    (hRH : ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 →
      0 ≤ s.im → s.im ≤ 10 ^ 5 → s.re = 1/2)
    (y : ℝ) (hy : Real.exp 23 ≤ y) (hY : y < Real.exp 136) :
    |Chebyshev.psi y - y| ≤ y / (40 * Real.log y) := by sorry
