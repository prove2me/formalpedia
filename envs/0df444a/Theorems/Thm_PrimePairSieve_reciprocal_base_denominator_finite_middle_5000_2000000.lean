-- Prove2me | Theorems.Thm_PrimePairSieve_reciprocal_base_denominator_finite_middle_5000_2000000
-- name    : PrimePairSieve.reciprocal_base_denominator_finite_middle_5000_2000000
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T19:32:20.953656+00:00
-- url     : https://prove2.me/theorems/36283906-8ebc-4f82-8939-6473c0c94b3f
-- title:
--   Remaining reciprocal sieve threshold on [5000,2000000]
-- statement:
--   This is the remaining finite certificate obligation for the existing reciprocal sieve threshold. For every real $5000\le z\le2000000$, the literal squarefree reciprocal sum must dominate the same threshold as the parent theorem. The real variable, natural-floor cutoff, twin-prime constant, and squarefree weights are unchanged. It is currently unproved. Together with the certified low intervals and the proved infinite tail, it suffices for the full parent threshold. An external numerical computation alone does not discharge it.
-- source:
--   Exact bounded restriction of https://prove2.me/theorems/dd059254-26a3-414d-be7b-44976fbe068b

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

theorem reciprocal_base_denominator_finite_middle_5000_2000000 :
    ∀ z : ℝ, 5000 ≤ z → z ≤ 2000000 →
      (Real.log (4 * z)) ^ 2 / (2 * TaoFivePrimes.twinPrimeConstant) /
          (1 - ((z + 1) * ((Real.log (4 * z)) ^ 2 /
            (2 * TaoFivePrimes.twinPrimeConstant)) / (16 * z ^ 2)))
        ≤ ∑ q ∈ Finset.Icc 1 ⌊z⌋₊,
          (if Squarefree q then
            ∏ p ∈ q.primeFactors, if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)
          else 0) / (1 + (q : ℝ) / z) := by sorry

end PrimePairSieve
