-- Prove2me | Theorems.Thm_WeakGoldbach_verified_range_pointwise_sieve_coverage
-- name    : WeakGoldbach.verified_range_pointwise_sieve_coverage
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-25T12:56:54.533339+00:00
-- url     : https://prove2.me/theorems/1a5bb549-a8c8-457e-a30b-83e6a3a028b6
-- title:
--   Pointwise small-prime sieve coverage through 4e18
-- statement:
--   For every even n with 4*10^14 <= n <= 4*10^18, there exist a prime p <= 9781 and an integer q in the survivor set for the interval [n-9781,n] at cutoff 2*10^9, such that p+q=n. This pointwise statement isolates the computational coverage assertion from the block-index and finite-set packaging.
-- source:
--   Pointwise form of WeakGoldbach.verified_range_sieve_coverage; interval and cutoff bounds follow the Oliveira e Silva-Herzog-Pardi verified Goldbach range through 4e18.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity

namespace WeakGoldbach
theorem verified_range_pointwise_sieve_coverage (n : Nat)
    (hlo : Nat.le (4 * 10 ^ 14) n) (hhi : Nat.le n (4 * 10 ^ 18)) (heven : Even n) :
    Exists fun p : Nat => Exists fun q : Nat =>
      And (Nat.Prime p) (And (Nat.le p 9781)
        (And (Membership.mem (GoldbachSieve.survivors (n - 9781) n 2000000000) q) (p + q = n))) := by
  sorry
end WeakGoldbach
