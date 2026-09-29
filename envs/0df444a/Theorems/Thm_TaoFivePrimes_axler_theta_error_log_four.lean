-- Prove2me | Theorems.Thm_TaoFivePrimes_axler_theta_error_log_four
-- name    : TaoFivePrimes.axler_theta_error_log_four
-- status  : Open
-- author  : @xuanji
-- created : 2026-09-27T22:42:37.71977+00:00
-- url     : https://prove2.me/theorems/79c840cc-14fb-4156-8dc6-a54d85771dad
-- title:
--   Axler explicit fourth-power logarithmic theta error
-- statement:
--   For every real $x\ge70111$, the Chebyshev theta function satisfies
--   $$|\vartheta(x)-x|<\frac{100x}{\log^4 x},\qquad \vartheta(x)=\sum_{p\le x}\log p.$$
--   This quantitative prime number theorem estimate is Proposition 1 of Axler (2018). It provides a reusable input for partial-summation estimates of reciprocal primes and Euler products. The statement includes the whole certified threshold range; the numerical verification and analytic estimates in the source remain to be formalized.
-- source:
--   Christian Axler, New Estimates for Some Functions Defined over Primes, Integers 18 (2018), A52, p. 6, Proposition 1, equation (2.4). https://math.colgate.edu/~integers/s52/s52.pdf

import Mathlib

theorem TaoFivePrimes.axler_theta_error_log_four (x : ℝ) (hx : 70111 ≤ x) :
  |(∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log (p : ℝ)) - x| <
    100 * x / (Real.log x) ^ 4 := by sorry
