-- Prove2me | Theorems.Thm_WeakGoldbach_ternary_goldbach_intermediate_range
-- name    : WeakGoldbach.ternary_goldbach_intermediate_range
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-25T13:53:52.847674+00:00
-- url     : https://prove2.me/theorems/310750a3-8383-4482-98da-c5c32cbb71a4
-- title:
--   Ternary Goldbach in the intermediate range
-- statement:
--   Let n be an odd integer with $$10^{27} \le n < e^{3100}.$$ The child theorem asserts that n can be written as a sum of three odd primes. This is the intermediate-range obligation in the proof decomposition for the ternary Goldbach theorem.
-- source:
--   H. A. Helfgott, The ternary Goldbach conjecture is true, arXiv:1312.7748, Theorem 1.

import Mathlib

namespace WeakGoldbach
theorem ternary_goldbach_intermediate_range (n : Nat) (hodd : Odd n) (hlo : 10 ^ 27 <= n) (hhi : (n : Real) < Real.exp 3100) :
    Exists fun p : Nat => Exists fun q : Nat => Exists fun r : Nat => And (Nat.Prime p) (And (Nat.Prime q) (And (Nat.Prime r) (And (Odd p) (And (Odd q) (And (Odd r) (n = p + q + r)))))) := by sorry
end WeakGoldbach
