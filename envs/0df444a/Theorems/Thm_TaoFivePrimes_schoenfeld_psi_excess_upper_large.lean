-- Prove2me | Theorems.Thm_TaoFivePrimes_schoenfeld_psi_excess_upper_large
-- name    : TaoFivePrimes.schoenfeld_psi_excess_upper_large
-- status  : Open
-- author  : @cm_beta
-- created : 2026-09-20T19:15:36.156239+00:00
-- url     : https://prove2.me/theorems/6a65fcdf-3229-40ae-b148-713c741ec80a
-- title:
--   Schoenfeld upper bound: $\psi(y)-y\le y/(40\log y)$ for $y\ge 10^8$
-- statement:
--   For every real $y \ge 10^{8}$ the second Chebyshev function does not exceed $y$ by more than $y/(40\log y)$:
--
--   $$\psi(y) - y \;\le\; rac{y}{40\log y}.$$
--
--   Here $\psi(y)=\sum_{n\le y}\Lambda(n)$ is the summatory von Mangoldt function. This is the **upper** half of Schoenfeld's two-sided explicit estimate: it bounds the excess of prime mass over the expected main term $y$. The statement is unconditional and assumes no form of the Riemann hypothesis. Together with the matching lower bound it yields the absolute-value form $|\psi(y)-y| \le y/(40\log y)$ used as the explicit prime-counting input in Tao's Lemma 4.3.
--
--   Separating the two directions reflects the structure of the original argument, in which the excess and the deficiency are controlled by different explicit computations.
-- source:
--   T. Tao, Every odd number greater than 1 is the sum of at most five primes, arXiv:1201.6656v4, Section 4, proof of Lemma 4.3 (https://arxiv.org/html/1201.6656v4), invoking L. Schoenfeld, Sharper bounds for the Chebyshev functions theta(x) and psi(x). II, Math. Comp. 30 (1976), Theorem 7. This lemma is the one-sided half of that two-sided estimate.

import Mathlib.NumberTheory.Chebyshev

namespace TaoFivePrimes

theorem schoenfeld_psi_excess_upper_large (y : ℝ) (hy : 10 ^ 8 ≤ y) :
    Chebyshev.psi y - y ≤ y / (40 * Real.log y) := by sorry

end TaoFivePrimes
