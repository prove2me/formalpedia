-- Prove2me | Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_integer_endpoint_certificate_low
-- name    : TaoFivePrimes.rosser_schoenfeld_theta_lower_integer_endpoint_certificate_low
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-09-25T14:05:31.271171+00:00
-- url     : https://prove2.me/theorems/f6a0e594-650b-423d-940d-4e021d44e9d5
-- title:
--   Finite integer endpoint certificate for the low theta range
-- statement:
--   For every integer n from 1420 through 10000, the Rosser-Schoenfeld lower-bound expression evaluated at the next integer is strictly below theta(n). This is the finite endpoint certificate needed to transfer the low-range estimate from integer floor intervals to real inputs.
-- source:
--   J. B. Rosser and L. Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois Journal of Mathematics 6 (1962), Theorem 4, equation (3.14), finite low-range endpoint certificate

import Mathlib.NumberTheory.Chebyshev

import Mathlib.NumberTheory.Chebyshev
namespace TaoFivePrimes
theorem rosser_schoenfeld_theta_lower_integer_endpoint_certificate_low (n : Nat) (h1 : 1420 <= n) (h2 : n <= 10000) :
    ((n : Real) + 1) * (1 - 1 / (2 * Real.log ((n : Real) + 1))) < Chebyshev.theta n := by sorry
end TaoFivePrimes
