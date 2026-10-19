-- Prove2me | Theorems.Thm_PrimeSum_sum_primes_card_le_log_sub_one
-- name    : PrimeSum.sum_primes_card_le_log_sub_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-18T14:51:07.216491+00:00
-- url     : https://prove2.me/theorems/9502dc0d-e408-48fd-96ce-11a32f79c2dd
-- title:
--   Every integer $n \ge 7$ is a sum of at most $\lfloor \log_2 n \rfloor - 1$ primes
-- statement:
--   Every natural number $n \ge 7$ is a sum of primes with at most $\lfloor \log_2 n \rfloor - 1$ summands.
--
--   Precisely: for every $n \ge 7$ there is a multiset $s$ of natural numbers such that every member of $s$ is prime, the members of $s$ sum to $n$, and
--
--   $$|s| \;\le\; \bigl\lfloor \log_2 n \bigr\rfloor - 1 .$$
--
--   This saves one more logarithm unit than the sharpened bound $\lfloor \log_2 n\rfloor$ of `PrimeSum.sum_primes_card_le_log_sharp`, and hence two more than the original bound $\lfloor \log_2 n\rfloor + 1$.
--
--   **Where the extra unit comes from.** The halving step replaces $n$ by $n - q$ with $q > n/2$, so the remainder satisfies $n - q \le n/2 - 1$ when $n$ is even and is strictly below $n/2$ always. Iterating, the remainder after $k$ summands is at most $n/2^k - (1 - 2^{-k})$, which is one unit below the naive halving estimate; the bound $\lfloor \log_2 n\rfloor - 1$ is exactly what that slack supports. Concretely, in the induction the case where the remainder is one of $2,3,4,5,6$ is the only place where the tightened hypothesis cannot be applied, and there three summands suffice, which is cheaper than $\lfloor\log_2 n\rfloor - 1$ whenever $n \ge 16$. The range $7 \le n \le 15$ is checked directly.
--
--   **Why it stops here.** Pushing the count one unit further fails at the bottom: $8 = 3 + 5$ needs two summands while $\lfloor \log_2 8\rfloor - 2 = 1$, so no statement of the form $\lfloor \log_2 n\rfloor - 2$ for all large $n$ follows from this method without a genuinely better prime-gap input.
--
--   **Formalization Note.** The subtraction $\lfloor \log_2 n\rfloor - 1$ is truncated subtraction on $\mathbb{N}$; the hypothesis $7 \le n$ makes it the genuine difference. Repetition of summands is allowed, as in the parent statements.
-- source:
--   P. Chebyshev, Memoire sur les nombres premiers (1852); Bertrand's postulate, formalized in Mathlib as Nat.exists_prime_lt_and_le_two_mul. Sharpens PrimeSum.sum_primes_card_le_log_sharp by one further logarithm unit, using the strict inequality n - q <= n/2 - 1 available in the halving step.

import Mathlib

namespace PrimeSum

theorem sum_primes_card_le_log_sub_one (n : ℕ) (hn : 7 ≤ n) :
  ∃ s : Multiset ℕ, (∀ p ∈ s, Nat.Prime p) ∧ s.sum = n ∧ s.card ≤ Nat.log 2 n - 1 := by sorry

end PrimeSum
