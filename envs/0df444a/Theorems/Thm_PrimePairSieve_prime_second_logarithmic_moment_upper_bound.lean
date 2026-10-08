-- Prove2me | Theorems.Thm_PrimePairSieve_prime_second_logarithmic_moment_upper_bound
-- name    : PrimePairSieve.prime_second_logarithmic_moment_upper_bound
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T14:43:46.277979+00:00
-- url     : https://prove2.me/theorems/d2ad8149-27b5-4766-a7d8-f4492cfe28a1
-- title:
--   Certified upper bound for the prime second logarithmic moment
-- statement:
--   The positive prime logarithmic moment
--
--   $$Q=\sum_{p\text{ prime}}\frac{8p^2-10p+4}{p^2(p-1)^2}\log^2p$$
--
--   is at most $8$. The bound includes the prime $2$. It supplies numerical control of the constant term in the ordinary and reciprocal prime-pair sieve expansions.
-- source:
--   A new rational numerical bound for the moment appearing in the proved PrimePairSieve.base_correction_second_logarithmic_moment and ordinary explicit expansion. Finite logarithm bounds and finite sum/integral comparisons from Mathlib; numerical constant chosen for the reciprocal-denominator tail comparison. Context: Riesel and Vaughan, On sums of primes (1983), Lemmas 2-3.

import Mathlib
open scoped BigOperators
set_option autoImplicit false

theorem PrimePairSieve.prime_second_logarithmic_moment_upper_bound :
    (∑' p : Nat.Primes,
      (8*(p:ℝ)^2-10*(p:ℝ)+4)/((p:ℝ)^2*((p:ℝ)-1)^2)*Real.log (p:ℝ)^2) ≤ 8 := by sorry
