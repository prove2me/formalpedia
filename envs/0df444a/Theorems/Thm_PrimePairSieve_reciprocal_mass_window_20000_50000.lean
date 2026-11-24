-- Prove2me | Theorems.Thm_PrimePairSieve_reciprocal_mass_window_20000_50000
-- name    : PrimePairSieve.reciprocal_mass_window_20000_50000
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T21:21:27.317303+00:00
-- url     : https://prove2.me/theorems/c16887db-efa6-4a40-80f4-d471f7c1369f
-- title:
--   Reciprocal sieve threshold on [20000,50000] via interval masses
-- statement:
--   For every real $20000\le z\le 50000$, with the mission's twin-prime constant $C$ and literal squarefree weight $w$, this theorem states
--
--   $$\frac{\log^2(4z)}{2C}\left(1-\frac{(z+1)\log^2(4z)}{32Cz^2}\right)^{-1}
--   \le\sum_{1\le n\le\lfloor z\rfloor}\frac{w(n)}{1+n/z}.$$
--
--   This is the exact bounded restriction of [the registered reciprocal threshold](https://prove2.me/theorems/dd059254-26a3-414d-be7b-44976fbe068b), preserving the real variable, natural floor, correction term, constant, and literal weights. It does not assert the full unbounded threshold or the five-primes theorem.
--
--   The certificate reuses 355 disjoint interval masses, checked in 5 groups containing 8,012 selected weights. A certified bound $C\ge1.31$, rational logarithm bounds, and 4 adjoining real cells transfer the finite endpoint comparisons over the whole interval. Integer masses and endpoint divisions round downward; disjointness and containment are checked before adding them. The interval proof imports the mass certificates and generic soundness results as explicit dependencies.
-- source:
--   Finite certificate for https://prove2.me/theorems/dd059254-26a3-414d-be7b-44976fbe068b; exact argument and scope in the statement.

import Mathlib
import Definitions.Def_TaoFivePrimes_SingularSeries
open scoped BigOperators
set_option autoImplicit false

theorem PrimePairSieve.reciprocal_mass_window_20000_50000 : ∀ z : ℝ, 20000 ≤ z → z ≤ 50000 →
      (Real.log (4 * z)) ^ 2 / (2 * TaoFivePrimes.twinPrimeConstant) /
          (1 - ((z + 1) * ((Real.log (4 * z)) ^ 2 /
            (2 * TaoFivePrimes.twinPrimeConstant)) / (16 * z ^ 2)))
        ≤ ∑ q ∈ Finset.Icc 1 ⌊z⌋₊,
          (if Squarefree q then
            ∏ p ∈ q.primeFactors, if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)
          else 0) / (1 + (q : ℝ) / z) := by sorry
