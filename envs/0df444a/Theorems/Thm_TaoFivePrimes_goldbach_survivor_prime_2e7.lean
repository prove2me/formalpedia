-- Prove2me | Theorems.Thm_TaoFivePrimes_goldbach_survivor_prime_2e7
-- name    : TaoFivePrimes.goldbach_survivor_prime_2e7
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-09-23T16:12:35.234121+00:00
-- url     : https://prove2.me/theorems/8d527ece-8501-4347-9f4c-9039645c0ef5
-- title:
--   Square-root completeness at the Richstein sieve cutoff: a survivor below (2·10⁷)² is prime
-- statement:
--   Let $N_0 = 4\cdot 10^{14} = (2\cdot 10^7)^2$. Suppose $2 \le n \le N_0$ and that no prime $p \le 2\cdot 10^7$ divides $n$. Then $n$ is prime.
--
--   This is the square-root completeness step of the sieve argument behind Richstein's verification: a survivor of sieving by all primes up to the cutoff $R = 2\cdot 10^7$ that lies at or below $R^2$ cannot be composite, since a composite $n \le R^2$ has a prime divisor at most $\sqrt{n} \le R$. It is the number-theoretic core that turns the finite sieve-coverage assertions (`Richstein2001.segmented_sieve_coverage`, stated in the `GoldbachSieve.pairSums` certificate language) into genuine Goldbach partitions, and it is stated here in self-contained form so that a proof worker can attack it with Mathlib alone.
-- source:
--   Five-primes mission; decomposes TaoFivePrimes.even_goldbach_verified (5247b31b-05f6-40f5-87b2-e5ce7b0e51f3). The sieve cutoff 2·10⁷ is the one used in Richstein2001.segmented_sieve_coverage; the completeness argument is standard (cf. J. Richstein, Verifying the Goldbach conjecture up to 4·10¹⁴, Math. Comp. 70 (2001), 1745–1749, https://doi.org/10.1090/S0025-5718-00-01290-4).

import Mathlib

set_option autoImplicit false

namespace TaoFivePrimes

theorem goldbach_survivor_prime_2e7 (n : ℕ) (h2 : 2 ≤ n) (hN : n ≤ 4 * 10 ^ 14)
    (hsurv : ∀ p : ℕ, p.Prime → p ≤ 20000000 → ¬ p ∣ n) :
    n.Prime := by sorry
end TaoFivePrimes
