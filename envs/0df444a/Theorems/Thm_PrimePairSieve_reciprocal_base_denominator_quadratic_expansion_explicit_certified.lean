-- Prove2me | Theorems.Thm_PrimePairSieve_reciprocal_base_denominator_quadratic_expansion_explicit_certified
-- name    : PrimePairSieve.reciprocal_base_denominator_quadratic_expansion_explicit_certified
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T13:18:39.178995+00:00
-- url     : https://prove2.me/theorems/19cc48fa-0e27-4d8a-af20-ebb90974f8d3
-- title:
--   Explicit reciprocal sieve denominator expansion from proved ordinary constants
-- statement:
--   Let $\gamma$ be Euler's constant, $P=\sum_p\log p/[p(p-1)]$, $Q=\sum_p(8p^2-10p+4)\log^2p/[p^2(p-1)^2]$, $u=2P+\tfrac12\log2$, and let $C$ be the twin-prime constant with its factor-two normalization. Define
--
--   $$L=2\gamma^2+4\gamma u+u^2+\tfrac14\log^22-Q-(4\gamma+4P+\log2)\log2+\frac{\pi^2}{6}.$$
--
--   For squarefree n put $w(n)=\prod_{p\mid n}w_p$, where $w_2=1$ and $w_p=2/(p-2)$ for odd primes; put $w(n)=0$ otherwise. There exist fixed $B\ge L$ and $0\le E\le127185/154$ such that every $z>0$ satisfies
--
--   $$\left|\sum_{1\le n\le z}\frac{w(n)}{1+n/z}-\frac{\log^2z+(4\gamma+4P-\log2)\log z+B}{2C}\right|\le E z^{-1/3}.$$
--
--   This gives an explicit reciprocal error constant from the already proved ordinary error bound 600, with the transformed constant term retained. It does not assert the stronger coefficient 10/3 or the threshold for every z at least 40.
-- source:
--   Proved ordinary input PrimePairSieve.base_denominator_quadratic_expansion_explicit (7d596122-b196-4342-b0e2-4582e418b754), transferred through the certified finite reciprocal-weight theorem. This is a new explicit consequence of proved inputs; it is not a quotation of the source paper's sharpest bounds. Context: Riesel and Vaughan, On sums of primes (1983), Lemmas 2-3.

import Mathlib
import Definitions.Def_TaoFivePrimes_SingularSeries
open scoped BigOperators
set_option autoImplicit false

theorem PrimePairSieve.reciprocal_base_denominator_quadratic_expansion_explicit_certified :
    ∃ B E : ℝ, 0 ≤ E ∧ E ≤ (127185 / 154 : ℝ) ∧
      (2 * Real.eulerMascheroniConstant^2 +
        4 * Real.eulerMascheroniConstant *
          (2 * (∑' p : Nat.Primes,
            Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) + Real.log 2 / 2) +
        ((2 * (∑' p : Nat.Primes,
            Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) + Real.log 2 / 2)^2 +
          (1 / 4 : ℝ) * Real.log 2^2 -
          (∑' p : Nat.Primes,
            (8 * (p : ℝ)^2 - 10 * (p : ℝ) + 4) /
              ((p : ℝ)^2 * ((p : ℝ) - 1)^2) * Real.log (p : ℝ)^2)) -
      (4 * Real.eulerMascheroniConstant +
        4 * (∑' p : Nat.Primes, Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) +
        Real.log 2) * Real.log 2 + Real.pi ^ 2 / 6 ≤ B) ∧
      (∀ z : ℝ, 0 < z →
        |(∑ n ∈ Finset.Icc 1 ⌊z⌋₊,
          (if Squarefree n then
            ∏ p ∈ n.primeFactors, if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)
          else 0) / (1 + (n : ℝ) / z)) -
        (Real.log z^2 +
          (4 * Real.eulerMascheroniConstant +
            4 * (∑' p : Nat.Primes,
              Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) - Real.log 2) *
            Real.log z + B) / (2 * TaoFivePrimes.twinPrimeConstant)| ≤
        E * z ^ (-(1 / 3 : ℝ))) := by sorry
