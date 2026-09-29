-- Prove2me | Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_finite_large_high_cert504
-- name    : TaoFivePrimes.rosser_schoenfeld_theta_lower_finite_large_high_cert504
-- status  : Proved
-- author  : @lt9
-- created : 2026-09-27T19:59:56.765614+00:00
-- url     : https://prove2.me/theorems/12f070a8-99e9-4808-94b9-9dcd44e903d5
-- title:
--   Rosser--Schoenfeld theta lower bound: high range, final sub-shard 504
-- statement:
--   For every integer $n$ with $99477217\le n\le99999999$, $(n+1)-2\sqrt{n+1}\le\theta(n)$, and the certificate's accumulated bound $A$ satisfies $A/2^{40}\le\theta(100000000)$; the hypothesis is the quantitative carry $B/2^{40}\le\theta(99477217)$ handed on by the previous shard. This is a final sub-shard of the finite endpoint certificate of the high sub-range $10^6\le t\le10^8$ in Rosser and Schoenfeld's Theorem 19.
-- source:
--   J. B. Rosser and L. Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois J. Math. 6 (1962), Theorem 19, p. 82, eq. (4.6), https://doi.org/10.1215/ijm/1255631807 (finite integer endpoint certificate, high sub-range 10^6 <= n <= 10^8, final split)

import Mathlib.NumberTheory.Chebyshev

namespace TaoFivePrimes
theorem rosser_schoenfeld_theta_lower_finite_large_high_cert504
    (hbase : (109361633821191791334 : Real) / 2 ^ 40 <= Chebyshev.theta (99477217 : Real))
    (n : Nat) (h1 : 99477217 <= n) (h2 : n <= 99999999) :
    (((n : Real) + 1) - 2 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\
      ((109937568534278953594 : Real) / 2 ^ 40 <= Chebyshev.theta (100000000 : Real)) := by sorry
end TaoFivePrimes
