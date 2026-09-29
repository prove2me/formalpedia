-- Prove2me | Theorems.Thm_WeakGoldbach_ternary_goldbach_all_odd
-- name    : WeakGoldbach.ternary_goldbach_all_odd
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-25T12:33:27.711778+00:00
-- url     : https://prove2.me/theorems/4e160e92-64f7-4655-94d2-59765f804d0c
-- title:
--   Helfgott ternary Goldbach theorem for all odd integers above 5
-- statement:
--   For every odd natural number n greater than 5, there are odd primes p, q, and r such that n = p + q + r. This is the full ternary Goldbach theorem proved by Helfgott.
-- source:
--   H. A. Helfgott, The ternary Goldbach conjecture is true, arXiv:1312.7748, Theorem 1.

import Mathlib

namespace WeakGoldbach
theorem ternary_goldbach_all_odd (n : Nat) (hgt : 5 < n) (hodd : Odd n) :
    Exists fun p : Nat => Exists fun q : Nat => Exists fun r : Nat =>
      And (Nat.Prime p) (And (Nat.Prime q) (And (Nat.Prime r)
        (And (Odd p) (And (Odd q) (And (Odd r) (n = p + q + r)))))) := by
  sorry
end WeakGoldbach
