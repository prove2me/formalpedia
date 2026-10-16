-- Prove2me | Theorems.Thm_TaoFivePrimes_rh_fast_center_polynomial_algebra
-- name    : TaoFivePrimes.rh_fast_center_polynomial_algebra
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-16T09:16:54.47839+00:00
-- url     : https://prove2.me/theorems/c82e04f9-f400-4cb6-8064-f4f3afe58138
-- title:
--   TaoFivePrimes.rh_fast_center_polynomial_algebra
-- statement:
--   The public center polynomial has degree at most28 and evaluates in the coordinate t/256 to the degree-four exponential polynomial of the degree-seven Stirling increment. This is an exact algebraic identity, with no numerical or RH assertion.
-- source:
--   Platt, Isolating some non-trivial zeros of zeta, DOI10.1090/mcom/3198; Gaussian/Hermite Fourier identities and center Stirling expansion. Original surrounding attribution retained: sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHFastGaussianWindowFourier

theorem TaoFivePrimes.rh_fast_center_polynomial_algebra (T:Nat) :
 (RHFastGaussianWindow.proxyPolynomial T).natDegree≤28 ∧
 ∀t:ℝ,(RHFastGaussianWindow.proxyPolynomial T).eval ((t:ℂ)/256)=
   RHFastGaussianWindow.exponentialPolynomial (RHFastGaussianWindow.delta T t) := by sorry
