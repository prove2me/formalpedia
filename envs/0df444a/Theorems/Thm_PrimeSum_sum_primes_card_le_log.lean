-- Prove2me | Theorems.Thm_PrimeSum_sum_primes_card_le_log
-- name    : PrimeSum.sum_primes_card_le_log
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-18T13:49:24.756975+00:00
-- url     : https://prove2.me/theorems/f74c4b49-75ea-4152-a645-89161b1cf5a4
-- title:
--   Every integer is a sum of at most log2(n)+1 primes
-- statement:
--   Every natural number $n \ge 2$ is a sum of primes with at most $\lfloor \log_2 n\rfloor + 1$ summands.
--
--   Precisely: there is a multiset $s$ of natural numbers such that every member of $s$ is prime, the members of $s$ sum to $n$, and the cardinality of $s$ — the number of summands counted with multiplicity — is at most $\lfloor\log_2 n\rfloor + 1$.
--
--   Repetition is allowed and no ordering or distinctness is imposed: $27$ is available as nine copies of $3$, and also as $3 + 11 + 13$. The bound is not claimed to be sharp; it is claimed to hold for every $n \ge 2$ with no further hypothesis.
--
--   This is the qualitative form of the question the platform's campaign *Odd numbers as sums of primes* tracks: a constant number of summands, as in Tao's five, Vinogradov's three in the large, and Helfgott's three, is a statement of a different order of depth; the logarithmic bound is the elementary rung beneath them and makes the dependence on $n$ explicit.
--
--   **Formalization Note.** At $n = 1$ no representation exists, so the hypothesis is $2 \le n$ and not $1 \le n$. The logarithm is the natural-number floor logarithm $\lfloor \log_2 \cdot \rfloor$.
-- source:
--   Standard: J. Bertrand (1845) and P. Chebyshev (1852), Bertrand postulate, formalized in Mathlib as Nat.exists_prime_lt_and_le_two_mul; the logarithmic bound is folklore along the lines of L. Schnirelmann, On the additive properties of numbers (1930), the first finite bound for sums of primes. Context: platform campaign "Odd numbers as sums of primes".

import Mathlib

namespace PrimeSum

theorem sum_primes_card_le_log (n : ℕ) (hn : 2 ≤ n) :
    ∃ s : Multiset ℕ, (∀ p ∈ s, Nat.Prime p) ∧ s.sum = n ∧ s.card ≤ Nat.log 2 n + 1 := by sorry

end PrimeSum
