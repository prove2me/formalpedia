-- Prove2me | Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_analytic_finite_mid
-- name    : TaoFivePrimes.rosser_schoenfeld_theta_lower_analytic_finite_mid
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-09-25T13:53:51.857493+00:00
-- url     : https://prove2.me/theorems/f938631c-0ed7-4525-8e5b-be26940bb7fd
-- title:
--   Rosser-Schoenfeld theta lower bound: 10,000 to 1,000,000
-- statement:
--   For every real t with 10^4 <= t <= 10^6, the Rosser-Schoenfeld lower bound t(1-1/(2 log t)) < theta(t) holds. This is the middle range component of the finite verification of Theorem 4, equation (3.14).
-- source:
--   J. B. Rosser and L. Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois Journal of Mathematics 6 (1962), Theorem 4, equation (3.14), finite subrange.

import Mathlib.NumberTheory.Chebyshev

namespace TaoFivePrimes
theorem rosser_schoenfeld_theta_lower_analytic_finite_mid (t : Real) (h1 : 10 ^ 4 <= t) (h2 : t <= 10 ^ 6) :
    t * (1 - 1 / (2 * Real.log t)) < Chebyshev.theta t := by sorry
end TaoFivePrimes
