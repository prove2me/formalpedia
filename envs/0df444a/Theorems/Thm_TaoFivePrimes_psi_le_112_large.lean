-- Prove2me | Theorems.Thm_TaoFivePrimes_psi_le_112_large
-- name    : TaoFivePrimes.psi_le_112_large
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-09T06:45:10.263986+00:00
-- url     : https://prove2.me/theorems/2d11a14e-062a-4c4d-a459-45500937e9a2
-- title:
--   Explicit Chebyshev bound on the five-primes range
-- statement:
--   For every real number $x$ satisfying $$10^{20}\le x\qquad\text{and}\qquad\log x\le3100,$$ the second Chebyshev function obeys the explicit estimate $$\psi(x)\le1.12x.$$ The range is tailored to the five-primes application. It avoids finite computation at small arguments and supplies a strong enough prime-counting estimate for the smoothed exponential-sum bound.
-- source:
--   Adapted from Alex Kontorovich et al., PrimeNumberTheoremAnd, IEANTN/Chebyshev.lean, commit a5154676af9aa3095150ee410cdda80555aa0642, especially psi_diff_upper and psi_upper_clean (lines 624–658). The restricted proof iterates psi_diff_upper twice and uses Mathlib Chebyshev.psi_le at x/36, eliminating the upstream LeanCert finite checker. https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/a5154676af9aa3095150ee410cdda80555aa0642/PrimeNumberTheoremAnd/IEANTN/Chebyshev.lean#L624-L658

import Mathlib.NumberTheory.Chebyshev

namespace TaoFivePrimes
theorem psi_le_112_large (x : ℝ) (hx : (10 : ℝ) ^ 20 ≤ x)
    (hlogx : Real.log x ≤ 3100) :
    Chebyshev.psi x ≤ 1.12 * x := by sorry
end TaoFivePrimes
