-- Prove2me | Theorems.Thm_PrimePairSieve_reciprocal_base_denominator_finite_middle_50000_2000000
-- name    : PrimePairSieve.reciprocal_base_denominator_finite_middle_50000_2000000
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T21:19:13.135719+00:00
-- url     : https://prove2.me/theorems/abd20997-f967-4386-9ab3-c468b41b228e
-- title:
--   Remaining reciprocal sieve threshold on [50000,2000000]
-- statement:
--   Let $C$ be the mission's twin-prime constant, and let $w(n)$ be zero for non-squarefree $n$ and otherwise the product over prime factors with factor $1$ at $2$ and $2/(p-2)$ at each odd prime $p$. The remaining finite assertion is that, for every real $50000\le z\le2000000$,
--
--   $$\frac{\log^2(4z)}{2C}\left(1-\frac{(z+1)\log^2(4z)}{32Cz^2}\right)^{-1}
--   \le\sum_{1\le n\le\lfloor z\rfloor}\frac{w(n)}{1+n/z}.$$
--
--   This is an explicitly Open obligation. It is the exact restriction of the [existing finite-middle target](https://prove2.me/theorems/36283906-8ebc-4f82-8939-6473c0c94b3f) to the range above 50,000. The real variable, natural floor, constant, correction term, and literal weights are unchanged. Once the low intervals are certified, this is the numerical gap before the already Proved infinite tail beginning at two million. An external arithmetic study is not a formal proof of this input.
-- source:
--   Exact bounded restriction of https://prove2.me/theorems/36283906-8ebc-4f82-8939-6473c0c94b3f

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

theorem reciprocal_base_denominator_finite_middle_50000_2000000 :
    ∀ z : ℝ, 50000 ≤ z → z ≤ 2000000 →
      (Real.log (4 * z)) ^ 2 / (2 * TaoFivePrimes.twinPrimeConstant) /
          (1 - ((z + 1) * ((Real.log (4 * z)) ^ 2 /
            (2 * TaoFivePrimes.twinPrimeConstant)) / (16 * z ^ 2)))
        ≤ ∑ q ∈ Finset.Icc 1 ⌊z⌋₊,
          (if Squarefree q then
            ∏ p ∈ q.primeFactors, if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)
          else 0) / (1 + (q : ℝ) / z) := by sorry

end PrimePairSieve
