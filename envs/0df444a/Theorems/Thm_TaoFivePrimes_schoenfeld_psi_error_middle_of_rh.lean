-- Prove2me | Theorems.Thm_TaoFivePrimes_schoenfeld_psi_error_middle_of_rh
-- name    : TaoFivePrimes.schoenfeld_psi_error_middle_of_rh
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T17:00:04.325201+00:00
-- url     : https://prove2.me/theorems/81e2636d-ba90-4380-8c29-7d2d2ae1d257
-- title:
--   Chebyshev psi error on the middle range from finite-height RH
-- statement:
--   Write $H=3.29\cdot10^9$. Assume that every zero $\rho$ of the Riemann zeta function satisfying $0<\operatorname{Re}\rho<1$ and $0\le\operatorname{Im}\rho\le H$ lies on the critical line $\operatorname{Re}\rho=1/2$. Then for every real $y$ with $e^{23}\le y<e^{136}$, the second Chebyshev function $\psi(y)=\sum_{n\le y}\Lambda(n)$ satisfies
--
--   $$|\psi(y)-y|\le\frac{y}{40\log y}.$$
--
--   This conditional intermediate covers the middle range needed to assemble the explicit Chebyshev error bound in Tao's five-primes argument. The hypothesis is precisely the zero-location clause of the existing finite-height verification; it does not assume the full Riemann hypothesis.
-- source:
--   Derived conditional intermediate for T. Tao, arXiv:1201.6656v4, Theorem 1.5 and Section 4, proof of Lemma 4.3, https://arxiv.org/html/1201.6656v4#S4. The hypothesis is exactly the zero-location clause of the finite-height RH input; the interval and explicit implication are an independently derived specialization, not a verbatim quotation. Uses the published Prove2Me smoothed Chebyshev formula and zero reciprocal bounds in ExplicitPNT.DusartTable1.

import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Exp

theorem TaoFivePrimes.schoenfeld_psi_error_middle_of_rh
    (hRH : ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 →
      0 ≤ s.im → s.im ≤ 3.29 * 10 ^ 9 → s.re = 1/2)
    (y : ℝ) (hy : Real.exp 23 ≤ y) (hY : y < Real.exp 136) :
    |Chebyshev.psi y - y| ≤ y / (40 * Real.log y) := by sorry
