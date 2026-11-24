-- Prove2me | Theorems.Thm_PrimePairSieve_base_denominator_quadratic_expansion_sharp
-- name    : PrimePairSieve.base_denominator_quadratic_expansion_sharp
-- status  : Open
-- author  : @andreaskapfer
-- created : 2026-09-23T13:09:56.052756+00:00
-- url     : https://prove2.me/theorems/68d7fa83-9016-475d-b96b-8b8a83f226b1
-- title:
--   Sharp explicit constants in the quadratic expansion of the prime-pair base sieve denominator
-- statement:
--   ## Statement
--
--   Let $S(z)$ denote the squarefree base sum
--   $$S(z)=\sum_{\substack{n\le z\\ n\ \mathrm{squarefree}}}\ \prod_{p\mid n} b_p,
--   \qquad b_2=1,\qquad b_p=\frac{2}{p-2}\ (p>2),$$
--   put
--   $$P=\sum_{p}\frac{\log p}{p(p-1)},\qquad
--   G=\sum_{p}\frac{8p^2-10p+4}{p^2(p-1)^2}\,\log^2 p,$$
--   let $\gamma$ be Euler's constant, and let $C$ be the twin-prime singular constant, normalized so that the Hardy--Littlewood prime-pair prediction is
--   $$C\prod_{p\mid d,\ p>2}\frac{p-1}{p-2}\cdot\frac{x}{\log^2 x}.$$
--
--   The theorem states that there exist real numbers $B$ and $E$ with
--   $$0\le E\le \tfrac{10}{3},\qquad B\ \ge\ 1.11,$$
--   such that for every real $z>0$
--   $$\Bigl|\,S(z)-\frac{\log^2 z+(4\gamma+4P+\log 2)\log z+B}{2C}\,\Bigr|\ \le\ E\,z^{-1/3}.$$
--
--   ## Meaning of the constants
--
--   This is the numerically sharp companion of the platform node `PrimePairSieve.base_denominator_quadratic_expansion_explicit` (itself the effective form of the quadratic expansion in Riesel--Vaughan, eqs. (3.6)--(3.10)). The centre is the Riesel--Vaughan quadratic asymptotic of the base sieve denominator, with the exact optimal choices of both remaining constants:
--
--   * the expansion constant is the value $2\gamma^2+4\gamma\bigl(2P+\tfrac{\log 2}{2}\bigr)+\bigl[\bigl(2P+\tfrac{\log 2}{2}\bigr)^2+\tfrac{\log^2 2}{4}-G\bigr]-4\gamma_1$, where $\gamma_1$ is the first Stieltjes constant; numerically it is $1.1141292\ldots$, so $B=1.1141292\ldots\ge 1.11$ is admissible;
--   * the true maximal size of the normalized error $\bigl|S(z)-\text{centre}(z)\bigr|\,z^{1/3}$ is $\approx 3.11$ (attained near $z\approx 42$), so $E=10/3$ is admissible with room to spare.
--
--   A direct numerical check confirms that for $B=1.1141292\ldots$ one has $\bigl|S(z)-\text{centre}(z)\bigr|\,z^{1/3}\le 3.1051$ for all integer $z\le 2\cdot 10^6$ and on a fine grid for real $z$, while for all $z$ below the grid the bound is far smaller.
--
--   ## Route
--
--   Together with the pure-analysis transfer lemma
--   $$\Bigl|\sum_{n\le z}\frac{b(n)n}{z+n}-\frac{2\log 2}{2C}\log z-\frac{4\gamma_1}{2C}\Bigr|\ \le\ \Bigl(\tfrac12+J\Bigr)\,E\,z^{-1/3},\qquad J=\int_0^1\frac{s^{-1/3}}{(1+s)^2}\,ds\approx 0.4,$$
--   this statement implies its reciprocal counterpart `PrimePairSieve.reciprocal_base_denominator_quadratic_expansion_sharp` with $E=3$, and hence (via the platform node `PrimePairSieve_prime_pair_count_base_reciprocal_bound`) the target `TaoFivePrimes.siebert_prime_pair_bound` in the range $x\ge 25600$, the remaining finite range being certified separately.
--
--   ## Reference
--
--   H. Riesel and R. C. Vaughan, *On sums of primes*, Arkiv för Matematik **21** (1983), 46--74, eqs. (3.6)--(3.10). Effective sharp version of the platform node `PrimePairSieve.base_denominator_quadratic_expansion`.
-- source:
--   H. Riesel and R. C. Vaughan, On sums of primes, Ark. Mat. 21 (1983), 46-74, eqs. (3.6)-(3.10); sharp explicit strengthening of platform node PrimePairSieve.base_denominator_quadratic_expansion.

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

theorem base_denominator_quadratic_expansion_sharp :
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
        E * z ^ (-(1 / 3 : ℝ))) := by sorry

end PrimePairSieve
