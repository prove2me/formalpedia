-- Prove2me | Theorems.Thm_PrimePairSieve_reciprocal_base_denominator_quadratic_expansion_sharp_transfer
-- name    : PrimePairSieve.reciprocal_base_denominator_quadratic_expansion_sharp_transfer
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-25T14:24:26.452885+00:00
-- url     : https://prove2.me/theorems/419e32c9-10c1-497e-8947-f28a5649fc70
-- title:
--   Transfer the sharp base expansion to the reciprocal denominator
-- statement:
--   Suppose constants $B_0,E_0$ give the ordinary squarefree base sum the quadratic expansion with linear coefficient $4\gamma+4P+\log 2$, error at most $E_0 z^{-1/3}$, and $B_0\ge 1.11$, where $P=\sum_p \log(p)/(p(p-1))$. The transfer theorem asserts that the reciprocal-kernel sum with weight $1/(1+n/z)$ then has an expansion whose linear coefficient is $4\gamma+4P-\log 2$, with some constants $B,E$ satisfying $B\ge-3/2$ and $0\le E\le10/3$. This isolates the analytic passage from the ordinary sum to its logarithmically averaged form.
-- source:
--   Transfer step for the explicit reciprocal-denominator expansion, following the route stated for PrimePairSieve.reciprocal_base_denominator_quadratic_expansion_sharp; see Riesel and Vaughan, On sums of primes, Ark. Mat. 21 (1983), equations (3.6)–(3.10).

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
theorem reciprocal_base_denominator_quadratic_expansion_sharp_transfer (h : (
∃ B E : ℝ, 0 ≤ E ∧ E ≤ 10 / 3 ∧ (1.11 : ℝ) ≤ B ∧
      (∀ z : ℝ, 0 < z →
        |(∑ n ∈ Finset.Icc 1 ⌊z⌋₊,
          if Squarefree n then
            ∏ p ∈ n.primeFactors, if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)
          else 0) -
        (Real.log z^2 +
          (4 * Real.eulerMascheroniConstant +
            4 * (∑' p : Nat.Primes,
              Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) + Real.log 2) *
            Real.log z + B) / (2 * TaoFivePrimes.twinPrimeConstant)| ≤
        E * z ^ (-(1 / 3 : ℝ)))
)) : (
∃ B E : ℝ, 0 ≤ E ∧ E ≤ 10 / 3 ∧ (-(3 / 2) : ℝ) ≤ B ∧
      (∀ z : ℝ, 0 < z →
        |(∑ n ∈ Finset.Icc 1 ⌊z⌋₊,
          (if Squarefree n then
            ∏ p ∈ n.primeFactors, if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)
          else 0) / (1 + (n : ℝ) / z)) -
        (Real.log z ^ 2 +
          (4 * Real.eulerMascheroniConstant +
            4 * (∑' p : Nat.Primes,
              Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) - Real.log 2) *
            Real.log z + B) / (2 * TaoFivePrimes.twinPrimeConstant)| ≤
        E * z ^ (-(1 / 3 : ℝ)))
) := by sorry
end PrimePairSieve
