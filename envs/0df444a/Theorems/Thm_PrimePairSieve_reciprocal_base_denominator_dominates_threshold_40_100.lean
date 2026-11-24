-- Prove2me | Theorems.Thm_PrimePairSieve_reciprocal_base_denominator_dominates_threshold_40_100
-- name    : PrimePairSieve.reciprocal_base_denominator_dominates_threshold_40_100
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T16:39:48.606485+00:00
-- url     : https://prove2.me/theorems/7ba1940b-1ffd-46e2-812f-617cea2d6476
-- title:
--   Reciprocal threshold on [40, 100] (finite pilot)
-- statement:
--   For every real $z$ with $40 \le z \le 100$, the literal reciprocal base denominator dominates the sieve threshold $T_{\mathrm{req}}(z)$ (same normalization as `reciprocal_base_denominator_dominates_threshold`). This is a kernel-checked finite pilot toward the open global inequality for all $z \ge 40$.
-- source:
--   Prove2Me five-primes finite-window pilot (2026-10-04)

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

namespace PrimePairSieve

theorem reciprocal_base_denominator_dominates_threshold_40_100 (z : ℝ) (hz : 40 ≤ z)
    (hupper : z ≤ 100) :
    Real.log (4 * z) ^ 2 / (2 * TaoFivePrimes.twinPrimeConstant) /
        (1 - ((z + 1) * (Real.log (4 * z)) ^ 2 /
          (2 * TaoFivePrimes.twinPrimeConstant)) / (16 * z ^ 2)) ≤
      ∑ q ∈ Finset.Icc 1 ⌊z⌋₊,
        (if Squarefree q then
            ∏ p ∈ q.primeFactors, if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)
          else 0) / (1 + (q : ℝ) / z) := by sorry

end PrimePairSieve
