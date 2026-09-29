-- Prove2me | Theorems.Thm_WeakGoldbach_ternary_goldbach_helfgott_above_10pow27
-- name    : WeakGoldbach.ternary_goldbach_helfgott_above_10pow27
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-25T14:08:27.31805+00:00
-- url     : https://prove2.me/theorems/92eb404b-da18-451f-b31d-f3637b1be79b
-- title:
--   Ternary Goldbach above 10^27
-- statement:
--   Every odd natural number n at least 10^27 can be written as a sum of three odd primes.
-- source:
--   Helfgott, The ternary Goldbach conjecture is true, arXiv:1312.7748, Theorem 1, restricted to n >= 10^27.

import Mathlib

namespace WeakGoldbach
theorem ternary_goldbach_helfgott_above_10pow27 (n : Nat) (hodd : Odd n) (hlo : 10 ^ 27 <= n) :
    Exists fun p : Nat => Exists fun q : Nat => Exists fun r : Nat =>
      And (Nat.Prime p) (And (Nat.Prime q) (And (Nat.Prime r)
        (And (Odd p) (And (Odd q) (And (Odd r) (n = p + q + r)))))) := by sorry
end WeakGoldbach
