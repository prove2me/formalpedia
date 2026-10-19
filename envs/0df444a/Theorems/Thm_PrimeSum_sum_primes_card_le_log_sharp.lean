-- Prove2me | Theorems.Thm_PrimeSum_sum_primes_card_le_log_sharp
-- name    : PrimeSum.sum_primes_card_le_log_sharp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-18T14:51:05.104296+00:00
-- url     : https://prove2.me/theorems/90d37832-df5f-4176-9d05-98b6de543d2e
-- title:
--   Every integer $n \ge 2$ is a sum of at most $\lfloor \log_2 n \rfloor$ primes
-- statement:
--   Every natural number $n \ge 2$ is a sum of primes with at most $\lfloor \log_2 n \rfloor$ summands.
--
--   Precisely: there is a multiset $s$ of natural numbers such that every member of $s$ is prime, the members of $s$ sum to $n$, and
--
--   $$|s| \;\le\; \bigl\lfloor \log_2 n \bigr\rfloor .$$
--
--   This is one logarithm unit better than the bound $\lfloor \log_2 n\rfloor + 1$ of the platform theorem `PrimeSum.sum_primes_card_le_log`, and it implies that theorem. The extra unit was bookkeeping, not content: in the halving induction that proves both, the induction hypothesis for the remainder already costs one unit, and the trailing $+1$ was never spent.
--
--   **Why the base of the logarithm does not move.** One summand is spent to halve what remains: Bertrand's postulate provides a prime $q$ with $n/2 < q \le n$, so the remainder $n - q$ is at most $n/2 - 1$ for even $n$ and strictly below $n/2$ always. One summand therefore buys a little more than one halving, and $2$ is the base that Bertrand's interval supports. Beating it means shrinking $n$ by a factor larger than $2$ per summand, which requires a prime in every interval $(n(1-\alpha), n]$ with $\alpha < \tfrac12$ — that is, a prime-gap estimate strictly stronger than Bertrand's. The classical instance is Nagura's theorem, a prime in $(\tfrac56 n, n]$ for $n \ge 25$, which would give the base $6$ and hence at most $\lfloor \log_6 n\rfloor$ summands; it needs explicit Chebyshev-type bounds for $\theta$ sharper than any in the library, and is not used here.
--
--   **Formalization Note.** Repetition is allowed, order is irrelevant, and distinctness is not required, exactly as in the parent statement. The logarithm is the natural-number floor logarithm `Nat.log 2 n`. At $n = 2$ the bound is $\lfloor \log_2 2\rfloor = 1$ and is attained, so it cannot be lowered further at the bottom.
-- source:
--   P. Chebyshev, Memoire sur les nombres premiers (1852); Bertrand's postulate, formalized in Mathlib as Nat.exists_prime_lt_and_le_two_mul. Sharpens the platform theorem PrimeSum.sum_primes_card_le_log by removing the additive constant; the halving argument is the one in the mission Sums of primes I.

import Mathlib

namespace PrimeSum

theorem sum_primes_card_le_log_sharp (n : ℕ) (hn : 2 ≤ n) :
  ∃ s : Multiset ℕ, (∀ p ∈ s, Nat.Prime p) ∧ s.sum = n ∧ s.card ≤ Nat.log 2 n := by sorry

end PrimeSum
