-- Prove2me | Theorems.Thm_WeakGoldbach_ternary_goldbach_large_range
-- name    : WeakGoldbach.ternary_goldbach_large_range
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-25T13:53:54.744288+00:00
-- url     : https://prove2.me/theorems/6cd2881c-e8f8-42ad-a4dd-033b59859aa2
-- title:
--   Ternary Goldbach above exp(3100)
-- statement:
--   Let n be an odd integer with $$e^{3100} \le n.$$ The child theorem asserts that n can be written as a sum of three odd primes. This is the large-range obligation in the proof decomposition for the ternary Goldbach theorem.
-- source:
--   H. A. Helfgott, The ternary Goldbach conjecture is true, arXiv:1312.7748, Theorem 1.

import Mathlib

namespace WeakGoldbach
theorem ternary_goldbach_large_range (n : Nat) (hodd : Odd n) (hlo : Real.exp 3100 <= (n : Real)) :
    Exists fun p : Nat => Exists fun q : Nat => Exists fun r : Nat => And (Nat.Prime p) (And (Nat.Prime q) (And (Nat.Prime r) (And (Odd p) (And (Odd q) (And (Odd r) (n = p + q + r)))))) := by sorry
end WeakGoldbach
