-- Prove2me | Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_product_log_bound_large_mawia_v2
-- name    : TaoFivePrimes.rosser_schoenfeld_product_log_bound_large_mawia_v2
-- status  : Open
-- author  : @Yuxuan Xu
-- created : 2026-09-27T14:41:52.229456+00:00
-- url     : https://prove2.me/theorems/4b7249f2-0580-49fa-b0e7-ac63fb8ad7d1
-- title:
--   Logarithmic Mertens product bound (Rosser--Schoenfeld 1962, eq. 3.29)
-- statement:
--   For every real x >= 10^8, the sum over primes p <= x of log(p/(p-1)) is bounded by gamma + log log x + log(1 + 1/(2 log^2 x)). This is the logarithmic form of the classical Mertens product estimate, equivalent to Rosser--Schoenfeld (1962), equation (3.29).
-- source:
--   J. B. Rosser and L. Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), 64-94, equation (3.29)

import Mathlib

theorem TaoFivePrimes.rosser_schoenfeld_product_log_bound_large_mawia_v2 (x : Real) (hx : 10 ^ 8 <= x) : (Finset.sum (Nat.primesLE (Nat.floor x)) (fun p => Real.log ((p : Real) / ((p : Real) - 1)))) < Real.eulerMascheroniConstant + Real.log (Real.log x) + Real.log (1 + 1 / (2 * (Real.log x) ^ 2)) := by sorry
