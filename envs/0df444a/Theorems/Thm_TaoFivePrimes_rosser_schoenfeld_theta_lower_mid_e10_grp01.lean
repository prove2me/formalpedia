-- Prove2me | Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_grp01
-- name    : TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp01
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-09T22:13:37.050782+00:00
-- url     : https://prove2.me/theorems/8c76a496-3ef1-4e23-abdf-08147eef95c9
-- title:
--   Rosser--Schoenfeld (3.14) finite range $10^9< t\le 10^{10}$: certificate block 1 of 27 (segments 1-50)
-- statement:
--   Let $\theta(x)=\sum_{p\le x}\log p$ be the Chebyshev theta function ($p$ prime, $\log$ natural), and suppose the integer $B=1099469019730663974882$ satisfies $B/2^{40}\le\theta(1000000001)$.
--
--   Then for every integer $n$ with $1000000001\le n\le 1312834711$,
--
--   $$
--   (n+1)-10\sqrt{n+1}\le\theta(n),
--   $$
--
--   and moreover the integer $A=1443427307425134654554$ satisfies $A/2^{40}\le\theta(1312834712)$.
--
--   Role: this is block $1$ of $27$ consecutive blocks covering $10^9<n\le 10^{10}$, the finite verification behind the range $10^9< t\le 10^{10}$ of Rosser and Schoenfeld's inequality (3.14), $t\,(1-1/(2\log t))<\theta(t)$ (Theorem 4), used by the node `TaoFivePrimes.rosser_schoenfeld_theta_lower_analytic_mid`. The block spans exactly the range of the integer certificate segments `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0001` through `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0050` (segments $1$ to $50$ of $1348$) and has the same form as those segments, so consecutive blocks chain the same way. Since $\theta$ is constant between consecutive integers, the bound at the integers $n$ with $n\le t<n+1$ gives the bound for real $t$, and $20\sqrt t<t/(2\log t)$ holds for $t\ge10^8$. The hypothesis is the lower bound for $\theta$ handed on by the previous block (for the first block it is the second conjunct of `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_grp03`, the last block of the range $10^8\le n\le10^9$); the second conjunct is the lower bound this block hands to the next one. Both conjuncts are unconditional finite statements about the primes up to $1312834712$.
--
--   **Formalization Note** The constant $10$ in front of $\sqrt{n+1}$ is a formalization choice: it is weaker than the $2\sqrt{t}$ of Rosser--Schoenfeld's Theorem 19 (which is stated only up to $10^8$) and is all that (3.14) needs on this range. The block endpoints and the integers $A$, $B$ are the exact values produced by the certificate chain; block $k$'s $A$ is block $k+1$'s $B$.
-- source:
--   J. B. Rosser and L. Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois Journal of Mathematics 6 (1962), 64--94, Theorem 4, p. 70, eq. (3.14), https://doi.org/10.1215/ijm/1255631807 (finite verification of the range 10^9 < t <= 10^10, certificate block 1 of 27 = integer certificate segments 1-50 of 1348; the finite part of the Five Primes node TaoFivePrimes.rosser_schoenfeld_theta_lower_analytic_mid, used in T. Tao, arXiv:1201.6656, Section 9)

import Mathlib.NumberTheory.Chebyshev

namespace TaoFivePrimes

theorem rosser_schoenfeld_theta_lower_mid_e10_grp01
    (hbase : (1099469019730663974882 : Real) / 2 ^ 40 <= Chebyshev.theta (1000000001 : Real))
    (n : Nat) (h1 : 1000000001 <= n) (h2 : n <= 1312834711) :
    (((n : Real) + 1) - 10 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\
      ((1443427307425134654554 : Real) / 2 ^ 40 <= Chebyshev.theta (1312834712 : Real)) := by sorry

end TaoFivePrimes
