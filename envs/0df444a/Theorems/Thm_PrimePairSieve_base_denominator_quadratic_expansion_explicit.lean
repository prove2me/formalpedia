-- Prove2me | Theorems.Thm_PrimePairSieve_base_denominator_quadratic_expansion_explicit
-- name    : PrimePairSieve.base_denominator_quadratic_expansion_explicit
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-23T11:26:40.179379+00:00
-- url     : https://prove2.me/theorems/7d596122-b196-4342-b0e2-4582e418b754
-- title:
--   Explicit constants in the quadratic expansion of the prime-pair base sieve denominator
-- statement:
--   ## Statement
--
--   Let $S(z)$ denote the squarefree base sum
--   $$S(z)=\sum_{\substack{n\le z\\ n\ \mathrm{squarefree}}}\ \prod_{p\mid n} b_p,
--   \qquad b_2=1,\qquad b_p=\frac{2}{p-2}\ (p>2),$$
--   and put
--   $$P=\sum_{p}\frac{\log p}{p(p-1)},\qquad
--   G=\sum_{p}\frac{8p^2-10p+4}{p^2(p-1)^2}\,\log^2 p .$$
--   Let $\gamma$ be Euler's constant and let $C$ be the twin-prime singular constant, i.e. the constant for which the Hardy--Littlewood prediction for prime pairs is $C\prod_{p\mid d,\ p>2}\frac{p-1}{p-2}\cdot\frac{x}{\log^2 x}$, so that $C=2\prod_{p>2}\bigl(1-\frac1{(p-1)^2}\bigr)$.
--
--   The theorem states that there exist real numbers $B$ and $E$ with $0\le E\le 600$ and
--   $$B\ \ge\ 2\gamma^2+4\gamma\Bigl(2P+\tfrac{\log 2}{2}\Bigr)
--   +\Bigl[\Bigl(2P+\tfrac{\log 2}{2}\Bigr)^2+\tfrac{(\log 2)^2}{4}-G\Bigr],$$
--   such that for every real $z>0$,
--   $$\Bigl|\,S(z)-\frac{\log^2 z+(4\gamma+4P+\log 2)\log z+B}{2C}\,\Bigr|\ \le\ E\,z^{-1/3}.$$
--
--   ## Meaning of the constants
--
--   The centre of the expansion is the Riesel--Vaughan quadratic asymptotic of the base sieve denominator, and the two constants are made effective:
--
--   * the error constant can be taken to be $E=2M\le 600$, where $M=\sum_{n\ge1}|h(n)|\,n^{1/3}$ and $h$ is the multiplicative correction
--   $$h(p)=\frac{2}{p-2}-\frac2p,\qquad
--   h(p^2)=\frac1{p^2}-\frac{2b_p}{p},\qquad
--   h(p^3)=\frac{b_p}{p^2}\quad(p>2),$$
--   with $h(2^k)$ given by the same formulas with $b_2=1$, and $h\equiv 0$ on fourth powers; the factor $2$ is the sharp uniform error constant of the double-harmonic kernel, and $M<300$ is the platform bound for the $1/3$-moment of the correction;
--   * the stated lower bound for $B$ is the value of the expansion constant when the limiting Stieltjes-type constant in the kernel centre is replaced by its upper endpoint $0$; since that constant lies in $[-1/6,0]$, the lower bound is valid.
--
--   ## Reference
--
--   H. Riesel and R. C. Vaughan, *On sums of primes*, Arkiv för Matematik **21** (1983), 46--74 (expansion of the base sieve denominator, eqs. (3.6)--(3.10); the source uses the sharper remainder constant $1.641$ for the kernel, which is irrelevant for this effective statement).
--
--   This is the effective, numerically ranged strengthening of the platform node `PrimePairSieve.base_denominator_quadratic_expansion`, and is the first step of a large-$x$ route to `TaoFivePrimes.siebert_prime_pair_bound`.
-- source:
--   Riesel--Vaughan, On sums of primes, Ark. Mat. 21 (1983), 46--74, eqs. (3.6)--(3.10); effective strengthening of platform node PrimePairSieve.base_denominator_quadratic_expansion.

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

theorem base_denominator_quadratic_expansion_explicit :
    ∃ B E : ℝ, 0 ≤ E ∧ E ≤ 600 ∧
      (2 * Real.eulerMascheroniConstant^2 +
        4 * Real.eulerMascheroniConstant *
          (2 * (∑' p : Nat.Primes,
            Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) + Real.log 2 / 2) +
        ((2 * (∑' p : Nat.Primes,
            Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) + Real.log 2 / 2)^2 +
          (1 / 4 : ℝ) * Real.log 2^2 -
          (∑' p : Nat.Primes,
            (8 * (p : ℝ)^2 - 10 * (p : ℝ) + 4) /
              ((p : ℝ)^2 * ((p : ℝ) - 1)^2) * Real.log (p : ℝ)^2)) ≤ B) ∧
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
        E * z ^ (-(1 / 3 : ℝ))) := by sorry

end PrimePairSieve
