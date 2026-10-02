-- Prove2me | Theorems.Thm_TaoFivePrimes_axler_theta_log_four_finite_certificate
-- name    : TaoFivePrimes.axler_theta_log_four_finite_certificate
-- status  : Proved
-- author  : @lt9
-- created : 2026-09-28T14:01:01.332841+00:00
-- url     : https://prove2.me/theorems/d06c489c-ac2e-433f-b5da-7de0cd4ae978
-- title:
--   Axler theta error, finite range: $|\vartheta(x)-x|<100x/\log^4x$ for $70111\le x<10^8$
-- statement:
--   **The finite half of Axler's explicit fourth-power theta estimate.**
--
--   Let
--   $$\vartheta(x)=\sum_{p\le x}\log p$$
--   be the Chebyshev theta function, the sum running over the primes $p$ up to $\lfloor x\rfloor$. This node asserts the pointwise estimate
--
--   $$\bigl|\vartheta(x)-x\bigr|<\frac{100\,x}{\log^4 x}\qquad\text{for every real }70111\le x<10^8 .$$
--
--   It is the numerical half of Proposition 1 of Axler (2018), which is stated for all $x\ge70111$. Splitting that proposition at $x=10^8$ separates the two logically different ingredients: below $10^8$ the estimate is a finite verification (one has to control $\vartheta$ by explicit computation on the primes in the range), while above $10^8$ it is a consequence of analytic estimates for the zeros of $\zeta$. This node is the first ingredient.
--
--   **Role.** The constant $100$ and the threshold $70111$ are exactly the ones in the target statement, and the range $[70111,10^8)$ is precisely the range in which the target bound is not implied by the analytic estimate. The estimate is *tight where it starts*: at $x=70111$ one has $\vartheta(x)-x\approx-442.86$ while $100x/\log^4x\approx452.34$, so the pointwise inequality holds with a margin of only about $2\%$ at the left endpoint, and no smaller constant would do at that point. This is why the numerical verification cannot be replaced by a weaker explicit bound: every published elementary estimate for $\vartheta$ (for instance $\vartheta(x)>x-2\sqrt x$, which is available on the platform for $1423\le x\le10^8$) is off by a factor $\sqrt x\log^3x/100$ from the required accuracy, and is therefore useless here.
--
--   **Formalization Note.** The statement is unconditional, and it is stated for real $x$; the summand depends on $x$ only through $\lfloor x\rfloor$, so the assertion is a finite statement about the primes up to $10^8$. The companion node `TaoFivePrimes.axler_theta_log_four_tail` covers the complementary range $x\ge10^8$.
-- source:
--   Christian Axler, New Estimates for Some Functions Defined over Primes, Integers 18 (2018), A52, p. 6, Proposition 1, equation (2.4). https://math.colgate.edu/~integers/s52/s52.pdf -- restricted to the finite range 70111 <= x < 10^8.

import Mathlib
open Finset

theorem TaoFivePrimes.axler_theta_log_four_finite_certificate (x : ℝ) (h1 : 70111 ≤ x) (h2 : x < 10 ^ 8) :
  |(∑ p ∈ Nat.primesLE ⌊x⌋₊, Real.log (p : ℝ)) - x| <
    100 * x / (Real.log x) ^ 4 := by sorry
