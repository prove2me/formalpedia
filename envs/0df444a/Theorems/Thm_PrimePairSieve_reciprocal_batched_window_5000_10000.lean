-- Prove2me | Theorems.Thm_PrimePairSieve_reciprocal_batched_window_5000_10000
-- name    : PrimePairSieve.reciprocal_batched_window_5000_10000
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T19:32:06.632739+00:00
-- url     : https://prove2.me/theorems/7ed8df96-f1ed-4dbc-a6cc-40bef6e7eb8a
-- title:
--   Reciprocal sieve threshold on [5000,10000]
-- statement:
--   Let $C$ be the mission's twin-prime constant. Put $w(n)=0$ when $n$ is not squarefree; otherwise put $w(n)=\prod_{p\mid n}b_p$, where $b_2=1$ and $b_p=2/(p-2)$ for odd primes. For every real $5000\le z\le 10000$,
--
--   $$\frac{\log^2(4z)}{2C}\left(1-\frac{(z+1)\log^2(4z)}{32Cz^2}\right)^{-1}\le\sum_{1\le n\le\lfloor z\rfloor}\frac{w(n)}{1+n/z}.$$
--
--   This is an exact bounded restriction of the registered reciprocal threshold. It retains the real variable, floor cutoff, and literal squarefree weights. A certificate covers the interval by adjoining real cells. This bounded result does not assert the full unbounded threshold or the five-primes theorem.
-- source:
--   Bounded restriction of https://prove2.me/theorems/dd059254-26a3-414d-be7b-44976fbe068b. Uses the proved real-interval criterion https://prove2.me/theorems/399f4fad-953d-4b94-880a-84fb162caaa7 and kernel-checked factor and integer-sum certificates. No claim of a new analytic estimate.

import Definitions.Def_TaoFivePrimes_SingularSeries
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Squarefree
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Topology.Algebra.InfiniteSum.Real

open scoped BigOperators

namespace PrimePairSieve

theorem reciprocal_batched_window_5000_10000 :
    ∀ z : ℝ, 5000 ≤ z → z ≤ 10000 →
      (Real.log (4 * z)) ^ 2 / (2 * TaoFivePrimes.twinPrimeConstant) /
          (1 - ((z + 1) * ((Real.log (4 * z)) ^ 2 /
            (2 * TaoFivePrimes.twinPrimeConstant)) / (16 * z ^ 2)))
        ≤ ∑ q ∈ Finset.Icc 1 ⌊z⌋₊,
          (if Squarefree q then
            ∏ p ∈ q.primeFactors, if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)
          else 0) / (1 + (q : ℝ) / z) := by sorry

end PrimePairSieve
