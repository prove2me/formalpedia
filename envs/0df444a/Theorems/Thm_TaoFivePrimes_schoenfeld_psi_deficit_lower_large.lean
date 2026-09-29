-- Prove2me | Theorems.Thm_TaoFivePrimes_schoenfeld_psi_deficit_lower_large
-- name    : TaoFivePrimes.schoenfeld_psi_deficit_lower_large
-- status  : Open
-- author  : @cm_beta
-- created : 2026-09-20T19:15:53.885983+00:00
-- url     : https://prove2.me/theorems/5c8762cc-96c9-41a7-96ee-3cd87c86eb7b
-- title:
--   Schoenfeld lower bound: $-(y/(40\log y))\le\psi(y)-y$ for $y\ge 10^8$
-- statement:
--   For every real $y \ge 10^{8}$ the second Chebyshev function falls short of $y$ by no more than $y/(40\log y)$:
--
--   $$-rac{y}{40\log y} \;\le\; \psi(y) - y.$$
--
--   Here $\psi(y)=\sum_{n\le y}\Lambda(n)$ is the summatory von Mangoldt function. This is the **lower** half of Schoenfeld's two-sided explicit estimate: it bounds the deficiency of prime mass relative to the main term $y$. The statement is unconditional and assumes no form of the Riemann hypothesis. Together with the matching upper bound it yields the absolute-value form $|\psi(y)-y| \le y/(40\log y)$ used as the explicit prime-counting input in Tao's Lemma 4.3.
--
--   Separating the two directions reflects the structure of the original argument, in which the excess and the deficiency are controlled by different explicit computations.
-- source:
--   T. Tao, Every odd number greater than 1 is the sum of at most five primes, arXiv:1201.6656v4, Section 4, proof of Lemma 4.3 (https://arxiv.org/html/1201.6656v4), invoking L. Schoenfeld, Sharper bounds for the Chebyshev functions theta(x) and psi(x). II, Math. Comp. 30 (1976), Theorem 7. This lemma is the one-sided half of that two-sided estimate.

import Mathlib.NumberTheory.Chebyshev

namespace TaoFivePrimes

theorem schoenfeld_psi_deficit_lower_large (y : ℝ) (hy : 10 ^ 8 ≤ y) :
    -(y / (40 * Real.log y)) ≤ Chebyshev.psi y - y := by sorry

end TaoFivePrimes
