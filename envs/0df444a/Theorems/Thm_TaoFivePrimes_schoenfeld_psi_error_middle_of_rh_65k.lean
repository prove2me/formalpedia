-- Prove2me | Theorems.Thm_TaoFivePrimes_schoenfeld_psi_error_middle_of_rh_65k
-- name    : TaoFivePrimes.schoenfeld_psi_error_middle_of_rh_65k
-- status  : Proved
-- author  : @Johan Mercedes
-- created : 2026-10-27T22:11:02.647802+00:00
-- url     : https://prove2.me/theorems/52972886-7c79-4851-9b88-526f260cf4e5
-- title:
--   Middle-range psi estimate from RH through height 65,000
-- statement:
--   Assume that every nontrivial zero of the Riemann zeta function with ordinate between $0$ and $65000$ lies on the critical line. Then, for every $e^{23}\le y<e^{136}$,
--
--   $$
--   |\psi(y)-y|\le\frac{y}{40\log y}.
--   $$
--
--   The finite-height Riemann hypothesis is an explicit assumption; this result does not assert its verification.
-- source:
--   Combines the middle-range reduction under finite-height RH and a sine-weight hypothesis with the separate sine-weight theorem developed for the Tao five-primes Chebyshev-error reduction.

import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

theorem TaoFivePrimes.schoenfeld_psi_error_middle_of_rh_65k
    (hRH : ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 →
      0 ≤ s.im → s.im ≤ 65000 → s.re = 1/2)
    (y : ℝ) (hy : Real.exp 23 ≤ y) (hY : y < Real.exp 136) :
    |Chebyshev.psi y - y| ≤ y / (40 * Real.log y) := by sorry
