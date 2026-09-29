-- Prove2me | Theorems.Thm_TaoFivePrimes_goldbach_sieve_witness_to_primes
-- name    : TaoFivePrimes.goldbach_sieve_witness_to_primes
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-09-23T16:12:17.247295+00:00
-- url     : https://prove2.me/theorems/2f0e5d5c-c9e2-4c7b-8f46-1a527c4c3d2b
-- title:
--   From a sieve witness p + q with q a survivor to a genuine Goldbach partition
-- statement:
--   Suppose $n = p + q$ where $p$ is a prime with $p \le 5569$, $2 \le q \le 4\cdot 10^{14}$, and $q$ is a survivor of sieving by the primes up to $2\cdot 10^7$: every prime $r \le 2\cdot 10^7$ dividing $q$ equals $q$ itself. Then $n$ is a sum of two primes.
--
--   This is the bridge between the certificate language of `Richstein2001.segmented_sieve_coverage` (membership in `GoldbachSieve.pairSums` with survivor sets defined by a no-small-prime-divisor condition) and the conclusion needed by `TaoFivePrimes.even_goldbach_verified`. The survivor predicate is restated inline in self-contained form; the bound $5569$ is the maximal smaller prime reported in Richstein's abstract. The proof is the square-root completeness argument: a composite $q \le (2\cdot 10^7)^2$ would have a prime divisor $r \le \sqrt{q} \le 2\cdot 10^7$ with $r < q$, contradicting the survivor condition, so $q$ itself is prime and $n = p + q$ is the required partition.
-- source:
--   Five-primes mission; decomposes TaoFivePrimes.even_goldbach_verified (5247b31b-05f6-40f5-87b2-e5ce7b0e51f3). Bridges Richstein2001.segmented_sieve_coverage (73281223-e520-4706-9186-a986548dc0d1) to per-block prime-pair witnesses; the maximal smaller prime 5569 is from J. Richstein, Verifying the Goldbach conjecture up to 4·10¹⁴, Math. Comp. 70 (2001), 1745–1749, https://doi.org/10.1090/S0025-5718-00-01290-4, abstract p. 1745. The survivor predicate is restated inline because Definitions.Def_GoldbachSieve is not elaborable in this workspace.

import Mathlib

set_option autoImplicit false

namespace TaoFivePrimes

theorem goldbach_sieve_witness_to_primes (n p q : ℕ)
    (hp : p.Prime) (hp5569 : p ≤ 5569) (hsum : p + q = n)
    (hq2 : 2 ≤ q) (hqN : q ≤ 4 * 10 ^ 14)
    (hsurv : ∀ r : ℕ, r.Prime → r ≤ 20000000 → r ∣ q → r = q) :
    ∃ p' q' : ℕ, p'.Prime ∧ q'.Prime ∧ p' + q' = n := by sorry
end TaoFivePrimes
