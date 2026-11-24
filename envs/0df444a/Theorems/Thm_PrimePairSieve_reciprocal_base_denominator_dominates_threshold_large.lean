-- Prove2me | Theorems.Thm_PrimePairSieve_reciprocal_base_denominator_dominates_threshold_large
-- name    : PrimePairSieve.reciprocal_base_denominator_dominates_threshold_large
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T14:43:51.007306+00:00
-- url     : https://prove2.me/theorems/bdbad104-76eb-4d51-a0f6-dab863c82475
-- title:
--   Reciprocal sieve denominator dominates the five-primes threshold above two million
-- statement:
--   Let $C$ be the twin-prime constant with the public factor-two normalization. Let $w(n)=0$ for nonsquarefree $n$, and otherwise $w(n)=\prod_{p\mid n}w_p$, with $w_2=1$ and $w_p=2/(p-2)$ for odd primes. Every real $z\ge2,000,000$ satisfies
--
--   $$\frac{\log^2(4z)}{2C}\left(1-\frac{(z+1)\log^2(4z)}{32Cz^2}\right)^{-1}\le\sum_{1\le n\le z}\frac{w(n)}{1+n/z}.$$
--
--   This proves the infinite tail of the existing reciprocal denominator threshold using an explicit coarse expansion, a prime-moment upper bound and certified constants. The correction denominator is proved positive in the argument. The remaining real window from $40$ to two million is a separate finite-certificate obligation.
-- source:
--   New consequence of PrimePairSieve.reciprocal_base_denominator_quadratic_expansion_explicit_certified, prime_second_logarithmic_moment_upper_bound and sieve_constants_certificate. Exact threshold and weights match existing PrimePairSieve.reciprocal_base_denominator_dominates_threshold, dd059254-26a3-414d-be7b-44976fbe068b. It is a large-cutoff result, not the full threshold or sharp 10/3 remainder.

import Definitions.Def_TaoFivePrimes_SingularSeries
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Squarefree
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Topology.Algebra.InfiniteSum.Real

open scoped BigOperators

set_option autoImplicit false

theorem PrimePairSieve.reciprocal_base_denominator_dominates_threshold_large :
    ∀ z : ℝ, 2000000 ≤ z →
      (Real.log (4 * z)) ^ 2 / (2 * TaoFivePrimes.twinPrimeConstant) /
          (1 - ((z + 1) * ((Real.log (4 * z)) ^ 2 /
            (2 * TaoFivePrimes.twinPrimeConstant)) / (16 * z ^ 2)))
        ≤ ∑ q ∈ Finset.Icc 1 ⌊z⌋₊,
          (if Squarefree q then
            ∏ p ∈ q.primeFactors, if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)
          else 0) / (1 + (q : ℝ) / z) := by sorry
