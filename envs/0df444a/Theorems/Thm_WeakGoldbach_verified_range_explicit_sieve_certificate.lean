-- Prove2me | Theorems.Thm_WeakGoldbach_verified_range_explicit_sieve_certificate
-- name    : WeakGoldbach.verified_range_explicit_sieve_certificate
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-25T13:52:20.25083+00:00
-- url     : https://prove2.me/theorems/818da556-1053-40b8-a9e8-55ff76b9e873
-- title:
--   Explicit small-prime sieve certificate for the verified range
-- statement:
--   For each even n in the stated verified interval, there is a prime p at most 9781 and a complement q=n-p in [max(2,n-9781),n] such that no prime r at most 2,000,000,000 divides q unless r=q. This explicit finite-filter formulation isolates the computational certificate behind the small-prime sieve survivor assertion.
-- source:
--   Pointwise certificate reformulation of WeakGoldbach.verified_range_pointwise_sieve_coverage, whose source records the Oliveira e Silva-Herzog-Pardi verified Goldbach range through 4e18.

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity

set_option autoImplicit false

namespace WeakGoldbach
theorem verified_range_explicit_sieve_certificate (n : Nat)
    (hlo : Nat.le (4 * 10 ^ 14) n) (hhi : Nat.le n (4 * 10 ^ 18)) (heven : Even n) :
    Exists fun p : Nat => Exists fun q : Nat =>
      And (Nat.Prime p) (And (Nat.le p 9781)
        (And (Membership.mem (Finset.Icc (max 2 (n - 9781)) n) q)
          (And (p + q = n)
            ((((Finset.Icc 2 2000000000).filter Nat.Prime).filter
              (fun r => And (Dvd.dvd r q) (Not (r = q)))) =
                (Finset.empty : Finset Nat))))) := by sorry
end WeakGoldbach
