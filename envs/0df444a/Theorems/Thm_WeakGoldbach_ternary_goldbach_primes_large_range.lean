-- Prove2me | Theorems.Thm_WeakGoldbach_ternary_goldbach_primes_large_range
-- name    : WeakGoldbach.ternary_goldbach_primes_large_range
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-25T14:23:20.001312+00:00
-- url     : https://prove2.me/theorems/5ed6ca66-6b6e-4509-a719-3ceb0a0d00d6
-- title:
--   Liu-Wang three-prime theorem above exp(3100)
-- statement:
--   For every odd natural number n at least exp(3100), there are primes p, q, and r, each greater than 2, whose sum is n. This is the large-range three-prime theorem of Liu and Wang; excluding 2 is equivalent to requiring odd primes and states the standard odd-integer version.
-- source:
--   M.-C. Liu and T.-Z. Wang, On the Vinogradov bound in the three primes Goldbach conjecture, Acta Arithmetica 105 (2002), 133-175, https://doi.org/10.4064/aa105-2-3.

import Mathlib

namespace WeakGoldbach
theorem ternary_goldbach_primes_large_range (n : Nat) (hodd : Odd n)
    (hlo : Real.exp 3100 <= (n : Real)) :
    Exists fun p : Nat => Exists fun q : Nat => Exists fun r : Nat =>
      And (Nat.Prime p) (And (Nat.Prime q) (And (Nat.Prime r)
        (And (2 < p) (And (2 < q) (And (2 < r) (n = p + q + r)))))) := by sorry
end WeakGoldbach
