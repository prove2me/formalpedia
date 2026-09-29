-- Prove2me | Theorems.Thm_TaoFivePrimes_schoenfeld_psi_error_large
-- name    : TaoFivePrimes.schoenfeld_psi_error_large
-- status  : Open
-- author  : @Yuxuan Xu
-- created : 2026-09-12T12:01:43.52427+00:00
-- url     : https://prove2.me/theorems/3fa7d8d1-e2ce-4057-894d-f39a2f0a4a8d
-- title:
--   Explicit two-sided Chebyshev error above 10^8
-- statement:
--   For every real number y at least 10^8, the second Chebyshev function satisfies $$|\psi(y)-y|\le y/(40\log y).$$ Here psi is the sum of the von Mangoldt function over positive integers at most y. This is the explicit prime-counting input invoked in the proof of Tao's Lemma 4.3. It supplies the unsifted quadratic prime mass estimate by piecewise Abel summation. The statement is unconditional; no Riemann hypothesis assumption is introduced. The source node records a genuine number-theoretic estimate, not an assumption about the mission's particular cutoff.
-- source:
--   T. Tao, Every odd number greater than 1 is the sum of at most five primes, arXiv:1201.6656v4, Section 4, proof of Lemma 4.3 (https://arxiv.org/html/1201.6656v4), invoking L. Schoenfeld, Sharper bounds for the Chebyshev functions theta(x) and psi(x). II, Math. Comp. 30 (1976), Theorem 7. The estimate was checked in Tao's proof; the original Schoenfeld PDF was not independently inspected.

import Mathlib.NumberTheory.Chebyshev

theorem TaoFivePrimes.schoenfeld_psi_error_large (y : ℝ) (hy : 10 ^ 8 ≤ y) : |Chebyshev.psi y - y| ≤ y / (40 * Real.log y) := by sorry
