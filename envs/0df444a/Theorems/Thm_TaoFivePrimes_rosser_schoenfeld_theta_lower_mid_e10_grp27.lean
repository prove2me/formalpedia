-- Prove2me | Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_grp27
-- name    : TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp27
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-10T06:42:51.143992+00:00
-- url     : https://prove2.me/theorems/4f76e689-754f-40f5-b48e-1deca74789c9
-- title:
--   Rosser--Schoenfeld (3.14) finite range $10^9< t\le 10^{10}$: certificate block 27 of 27 (segments 1300-1348)
-- statement:
--   Let $\theta(x)=\sum_{p\le x}\log p$ be the Chebyshev theta function ($p$ prime, $\log$ natural), and suppose the integer $B=10623356848875818030645$ satisfies $B/2^{40}\le\theta(9661975292)$.
--
--   Then for every integer $n$ with $9661975292\le n\le 10000000000$,
--
--   $$
--   (n+1)-10\sqrt{n+1}\le\theta(n),
--   $$
--
--   and moreover the integer $A=10995041617401890452312$ satisfies $A/2^{40}\le\theta(10000000001)$.
--
--   Role: this is block $27$ of $27$ consecutive blocks covering $10^9<n\le 10^{10}$, the finite verification behind the range $10^9< t\le 10^{10}$ of Rosser and Schoenfeld's inequality (3.14), $t\,(1-1/(2\log t))<\theta(t)$ (Theorem 4), used by the node `TaoFivePrimes.rosser_schoenfeld_theta_lower_analytic_mid`. The block spans exactly the range of the integer certificate segments `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1300` through `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg1348` (segments $1300$ to $1348$ of $1348$) and has the same form as those segments, so consecutive blocks chain the same way. Since $\theta$ is constant between consecutive integers, the bound at the integers $n$ with $n\le t<n+1$ gives the bound for real $t$, and $20\sqrt t<t/(2\log t)$ holds for $t\ge10^8$. The hypothesis is the lower bound for $\theta$ handed on by the previous block (it is the second conjunct of `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp26`); the second conjunct is the lower bound this block hands to the next one. Both conjuncts are unconditional finite statements about the primes up to $10000000001$.
--
--   **Formalization Note** The constant $10$ in front of $\sqrt{n+1}$ is a formalization choice: it is weaker than the $2\sqrt{t}$ of Rosser--Schoenfeld's Theorem 19 (which is stated only up to $10^8$) and is all that (3.14) needs on this range. The block endpoints and the integers $A$, $B$ are the exact values produced by the certificate chain; block $k$'s $A$ is block $k+1$'s $B$.
-- source:
--   J. B. Rosser and L. Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois Journal of Mathematics 6 (1962), 64--94, Theorem 4, p. 70, eq. (3.14), https://doi.org/10.1215/ijm/1255631807 (finite verification of the range 10^9 < t <= 10^10, certificate block 27 of 27 = integer certificate segments 1300-1348 of 1348; the finite part of the Five Primes node TaoFivePrimes.rosser_schoenfeld_theta_lower_analytic_mid, used in T. Tao, arXiv:1201.6656, Section 9)

import Mathlib.NumberTheory.Chebyshev

namespace TaoFivePrimes

theorem rosser_schoenfeld_theta_lower_mid_e10_grp27
    (hbase : (10623356848875818030645 : Real) / 2 ^ 40 <= Chebyshev.theta (9661975292 : Real))
    (n : Nat) (h1 : 9661975292 <= n) (h2 : n <= 10000000000) :
    (((n : Real) + 1) - 10 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\
      ((10995041617401890452312 : Real) / 2 ^ 40 <= Chebyshev.theta (10000000001 : Real)) := by sorry

end TaoFivePrimes
