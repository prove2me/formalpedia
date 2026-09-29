-- Prove2me | Theorems.Thm_WeakGoldbach_ternary_goldbach_small_range
-- name    : WeakGoldbach.ternary_goldbach_small_range
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-09-25T13:53:54.565724+00:00
-- url     : https://prove2.me/theorems/1249b51f-8755-4a89-9392-3a9a8a435cdc
-- title:
--   Ternary Goldbach below 10^27
-- statement:
--   Let n be an odd integer in the bounded range $$5 < n < 10^{27}.$$ The child theorem asserts that n can be written as a sum of three odd primes. This is the small-range obligation in the proof decomposition for the ternary Goldbach theorem.
-- source:
--   H. A. Helfgott, The ternary Goldbach conjecture is true, arXiv:1312.7748, Theorem 1.

import Mathlib

namespace WeakGoldbach
theorem ternary_goldbach_small_range (n : Nat) (hgt : 5 < n) (hodd : Odd n) (hsmall : n < 10 ^ 27) :
    Exists fun p : Nat => Exists fun q : Nat => Exists fun r : Nat => And (Nat.Prime p) (And (Nat.Prime q) (And (Nat.Prime r) (And (Odd p) (And (Odd q) (And (Odd r) (n = p + q + r)))))) := by sorry
end WeakGoldbach
