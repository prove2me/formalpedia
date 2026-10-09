-- Prove2me | Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0442
-- name    : TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0442
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-09T11:00:53.332873+00:00
-- url     : https://prove2.me/theorems/44583b5f-c9ce-4491-adbf-e8a2736e1bd7
-- title:
--   Rosser--Schoenfeld (3.14) finite range $10^9< t\le 10^{10}$: certificate segment 442 of 1348
-- statement:
--   Let $\theta(x)=\sum_{p\le x}\log p$ be the Chebyshev theta function ($p$ prime, $\log$ natural), and suppose the integer $B=4230927366590584242719$ satisfies $B/2^{40}\le\theta(3848059212)$.
--
--   Then for every integer $n$ with $3848059212\le n\le 3854678423$,
--
--   $$
--   (n+1)-10\sqrt{n+1}\le\theta(n),
--   $$
--
--   and moreover the integer $A=4238204297273557550781$ satisfies $A/2^{40}\le\theta(3854678424)$.
--
--   Role: this is segment $442$ of $1348$ consecutive segments covering $10^9<n\le 10^{10}$, the finite verification behind the range $10^9<t\le10^{10}$ of Rosser and Schoenfeld's inequality (3.14), $t\,(1-1/(2\log t))<\theta(t)$ (Theorem 4), which is the parent node `TaoFivePrimes.rosser_schoenfeld_theta_lower_analytic_mid`. Since $\theta$ is constant between consecutive integers, the bound at the integers $n$ with $n\le t<n+1$ gives the bound for real $t$, and $20\sqrt t<t/(2\log t)$ holds for $t\ge10^8$. The hypothesis is the lower bound for $\theta$ handed on by the previous segment (for the first segment it is the second conjunct of `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_lower_cert151`, the last segment of the range $10^8\le n\le10^9$); the second conjunct is the lower bound this segment hands to the next one. Both conjuncts are unconditional finite statements about the primes up to $3854678424$.
--
--   **Formalization Note** The constant $10$ in front of $\sqrt{n+1}$ is a formalization choice: it is weaker than the $2\sqrt{t}$ of Rosser--Schoenfeld's Theorem 19 (which is stated only up to $10^8$) and is all that (3.14) needs on this range. The segment endpoints and the integers $A$, $B$ are the exact values produced by the certificate chain; segment $k$'s $A$ is segment $k+1$'s $B$.
-- source:
--   J. B. Rosser and L. Schoenfeld, Approximate formulas for some functions of prime numbers, Illinois Journal of Mathematics 6 (1962), 64--94, Theorem 4, p. 70, eq. (3.14), https://doi.org/10.1215/ijm/1255631807 (finite verification of the range 10^9 < t <= 10^10, integer certificate segment 442 of 1348; the finite part of the Five Primes node TaoFivePrimes.rosser_schoenfeld_theta_lower_analytic_mid, used in T. Tao, arXiv:1201.6656, Section 9)

import Mathlib.NumberTheory.Chebyshev

namespace TaoFivePrimes

theorem rosser_schoenfeld_theta_lower_mid_e10_seg0442
    (hbase : (4230927366590584242719 : Real) / 2 ^ 40 <= Chebyshev.theta (3848059212 : Real))
    (n : Nat) (h1 : 3848059212 <= n) (h2 : n <= 3854678423) :
    (((n : Real) + 1) - 10 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\
      ((4238204297273557550781 : Real) / 2 ^ 40 <= Chebyshev.theta (3854678424 : Real)) := by sorry

end TaoFivePrimes
