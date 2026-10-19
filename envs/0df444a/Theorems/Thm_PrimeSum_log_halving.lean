-- Prove2me | Theorems.Thm_PrimeSum_log_halving
-- name    : PrimeSum.log_halving
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-18T13:49:24.898575+00:00
-- url     : https://prove2.me/theorems/60d93ea6-e292-465f-b592-24e3777944cd
-- title:
--   A summand above n/2 costs one unit of the logarithm
-- statement:
--   Let $n \ge 2$ be a natural number and let $p$ be a natural number with $\frac{n}{2} < p \le n$. Then
--
--   $$\bigl\lfloor \log_2 (n - p)\bigr\rfloor + 1 \ \le\ \bigl\lfloor \log_2 n\bigr\rfloor .$$
--
--   The content is that a summand larger than half of what remains costs one unit of the logarithm: the remainder $n - p$ is below $n/2$, so its floor logarithm is at most that of $n$ minus one.
--
--   This is the arithmetic step that makes the induction proving the logarithmic sum-of-primes bound terminate: choosing a prime in the upper half, which Bertrand's postulate guarantees, halves what remains at the price of one summand, and this inequality is what converts that halving into the budget $\lfloor\log_2 n\rfloor + 1$.
--
--   **Formalization Note.** Subtraction is truncated subtraction on the natural numbers; the hypothesis $\frac{n}{2} < p$ is expressed as $n < 2p$, and $p \le n$ makes $n - p$ the genuine difference.
-- source:
--   Standard: J. Bertrand (1845) and P. Chebyshev (1852), Bertrand postulate, formalized in Mathlib as Nat.exists_prime_lt_and_le_two_mul; the logarithmic bound is folklore along the lines of L. Schnirelmann, On the additive properties of numbers (1930), the first finite bound for sums of primes. Context: platform campaign "Odd numbers as sums of primes".

import Mathlib

namespace PrimeSum

theorem log_halving (n p : ℕ) (hn : 2 ≤ n) (hp : n < 2 * p) (hpn : p ≤ n) :
    Nat.log 2 (n - p) + 1 ≤ Nat.log 2 n := by sorry

end PrimeSum
