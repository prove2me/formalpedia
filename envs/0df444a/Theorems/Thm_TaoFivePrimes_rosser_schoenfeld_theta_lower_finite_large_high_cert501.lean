-- Prove2me | Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_finite_large_high_cert501
-- name    : TaoFivePrimes.rosser_schoenfeld_theta_lower_finite_large_high_cert501
-- status  : Proved
-- author  : @lt9
-- created : 2026-09-27T19:47:21.084676+00:00
-- url     : https://prove2.me/theorems/1554f3d1-7e30-4125-9f38-13d4a711f9ae
-- title:
--   Rosser--Schoenfeld theta lower bound: high range, final sub-shard 501
-- statement:
--   For every integer $n$ with $97540550\le n\le98961909$, $(n+1)-2\sqrt{n+1}\le\theta(n)$, and the certificate's accumulated bound $A$ satisfies $A/2^{40}\le\theta(98961910)$; the hypothesis is the quantitative carry $B/2^{40}\le\theta(97540550)$ handed on by the previous shard. This is a final sub-shard of the finite endpoint certificate of the high sub-range $10^6\le t\le10^8$ in Rosser and Schoenfeld's Theorem 19.
-- source:
--   J. B. Rosser and L. Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), Theorem 19, p. 82, eq. (4.6), https://doi.org/10.1215/ijm/1255631807 (finite integer endpoint certificate, high sub-range 10^6 <= n <= 10^8, final split)

import Mathlib.NumberTheory.Chebyshev

namespace TaoFivePrimes
theorem rosser_schoenfeld_theta_lower_finite_large_high_cert501
    (hbase : (107235796790648773720 : Real) / 2 ^ 40 <= Chebyshev.theta (97540550 : Real))
    (n : Nat) (h1 : 97540550 <= n) (h2 : n <= 98961909) :
    (((n : Real) + 1) - 2 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\
      ((108795660965686084466 : Real) / 2 ^ 40 <= Chebyshev.theta (98961910 : Real)) := by sorry
end TaoFivePrimes
