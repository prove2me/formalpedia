-- Prove2me | Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_finite_large_high_cert701
-- name    : TaoFivePrimes.rosser_schoenfeld_theta_lower_finite_large_high_cert701
-- status  : Proved
-- author  : @lt9
-- created : 2026-09-27T20:33:49.377519+00:00
-- url     : https://prove2.me/theorems/3502ee6a-042b-4e03-8db7-07987c546f8c
-- title:
--   Rosser--Schoenfeld theta lower bound: high range, bootstrap shard
-- statement:
--   For every integer $n$ with $10001\le n\le226652$, $(n+1)-2\sqrt{n+1}\le\theta(n)$, and the certificate's accumulated bound satisfies $A/2^{40}\le\theta(226653)$. This is the bootstrap shard of the finite endpoint certificate of the high sub-range $10^6\le t\le10^8$ in Rosser and Schoenfeld's Theorem 19 (started at the Chebyshev bootstrap $\theta(10^4)$); its second conjunct is the quantitative carry handed to the next shard.
-- source:
--   J. B. Rosser and L. Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), Theorem 19, p. 82, eq. (4.6), https://doi.org/10.1215/ijm/1255631807 (finite integer endpoint certificate, high sub-range 10^6 <= n <= 10^8, bootstrap shard)

import Mathlib.NumberTheory.Chebyshev

namespace TaoFivePrimes
theorem rosser_schoenfeld_theta_lower_finite_large_high_cert701 (n : Nat) (h1 : 10001 <= n) (h2 : n <= 226652) :
    (((n : Real) + 1) - 2 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\
      ((248661901352816209 : Real) / 2 ^ 40 <= Chebyshev.theta (226653 : Real)) := by sorry
end TaoFivePrimes
