-- Prove2me | Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_analytic_finite_low
-- name    : TaoFivePrimes.rosser_schoenfeld_theta_lower_analytic_finite_low
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-09-25T13:53:52.400514+00:00
-- url     : https://prove2.me/theorems/1fb0240a-bac7-4f9d-9f87-9b5f5ef1400d
-- title:
--   Rosser-Schoenfeld theta lower bound: 1420 to 10,000
-- statement:
--   For every real t with 1420 <= t <= 10^4, the Rosser-Schoenfeld lower bound t(1-1/(2 log t)) < theta(t) holds. This is the first range component of the finite verification of Theorem 4, equation (3.14).
-- source:
--   J. B. Rosser and L. Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois Journal of Mathematics 6 (1962), Theorem 4, equation (3.14), finite subrange.

import Mathlib.NumberTheory.Chebyshev

namespace TaoFivePrimes
theorem rosser_schoenfeld_theta_lower_analytic_finite_low (t : Real) (h1 : 1420 <= t) (h2 : t <= 10 ^ 4) :
    t * (1 - 1 / (2 * Real.log t)) < Chebyshev.theta t := by sorry
end TaoFivePrimes
