-- Prove2me | Theorems.Thm_PrimePairSieve_reciprocal_base_denominator_quadratic_expansion_sharp
-- name    : PrimePairSieve.reciprocal_base_denominator_quadratic_expansion_sharp
-- status  : Open
-- author  : @andreaskapfer
-- created : 2026-09-23T13:10:09.103111+00:00
-- url     : https://prove2.me/theorems/1cbbb7bc-148e-4be1-9f0f-d82fcb65c272
-- title:
--   Sharp explicit constants in the reciprocal base denominator expansion
-- statement:
--   ## Statement
--
--   Let $B(z)$ denote the reciprocal (logarithmically averaged) base denominator
--   $$B(z)=\sum_{\substack{n\le z\\ n\ \mathrm{squarefree}}}\ \frac{\prod_{p\mid n} b_p}{1+n/z},
--   \qquad b_2=1,\qquad b_p=\frac{2}{p-2}\ (p>2),$$
--   put
--   $$P=\sum_{p}\frac{\log p}{p(p-1)},\qquad
--   G=\sum_{p}\frac{8p^2-10p+4}{p^2(p-1)^2}\,\log^2 p,$$
--   let $\gamma$ be Euler's constant, and let $C$ be the twin-prime singular constant.
--
--   The theorem states that there exist real numbers $B$ and $E$ with
--   $$0\le E\le \tfrac{10}{3},\qquad B\ \ge\ -\tfrac32,$$
--   such that for every real $z>0$
--   $$\Bigl|\,B(z)-\frac{\log^2 z+(4\gamma+4P-\log 2)\log z+B}{2C}\,\Bigr|\ \le\ E\,z^{-1/3}.$$
--
--   ## Meaning of the constants
--
--   This is the explicit-constants, numerically sharp version of the platform node `PrimePairSieve.reciprocal_base_denominator_quadratic_expansion` (the logarithmic average of the base sieve denominator), which is exactly the denominator that appears in the application of the large sieve to prime pairs.
--
--   * The centre is the same quadratic asymptotic as in the ordinary base sum, with the logarithmic shift $4\gamma+4P-\log 2$ that arises from the kernel $1/(1+n/z)$. The optimal expansion constant is $B=2\gamma^2+4\gamma\bigl(2P+\tfrac{\log 2}{2}\bigr)+\bigl[\bigl(2P+\tfrac{\log 2}{2}\bigr)^2+\tfrac{\log^2 2}{4}-G\bigr]-4\gamma_1-\log 2\,(4\gamma+4P+\log 2)+\tfrac{\pi^2}{6}$, numerically $-1.4160909\ldots$; hence $B=-1.4160909\ldots\ge -\tfrac32$ is admissible.
--   * The true maximal size of the normalized error is only $\approx 1.98$ (attained near $z\approx 30$), so $E=10/3$ is admissible with a factor $1.7$ to spare.
--
--   A direct numerical check (both at all integers $z\le 2\cdot 10^6$ and on a grid of step $0.01$ for $z\le 300$, step $0.2$ up to $3000$, step $5$ up to $30000$) gives $\bigl|B(z)-\text{centre}(z)\bigr|\,z^{1/3}\le 1.9716$.
--
--   ## Route
--
--   Provable from `PrimePairSieve.base_denominator_quadratic_expansion_sharp` together with the pure-analysis transfer estimate for
--   $$\Delta(z)=\sum_{n\le z}\frac{b(n)n}{z+n}=S(z)-B(z),
--   \qquad \Delta(z)=\frac{2\log 2}{2C}\log z+\frac{4\gamma_1}{2C}+O\bigl(z^{-1/3}\bigr),$$
--   obtained by writing $n/(z+n)=\int_0^n z/(z+t)^2\,dt$ and inserting the errors of the ordinary expansion; the constant loss is $\tfrac12+J<0.9$, so the sharp estimate $E\le \tfrac{10}{3}$ for $S$ yields $E\le 3$ for $B$ (and in particular $\le 10/3$).
--
--   ## Reference
--
--   H. Riesel and R. C. Vaughan, *On sums of primes*, Arkiv för Matematik **21** (1983), 46--74, eqs. (3.6)--(3.10); explicit sharp version of the platform node `PrimePairSieve.reciprocal_base_denominator_quadratic_expansion`.
-- source:
--   H. Riesel and R. C. Vaughan, On sums of primes, Ark. Mat. 21 (1983), 46-74, eqs. (3.6)-(3.10); sharp explicit strengthening of platform node PrimePairSieve.reciprocal_base_denominator_quadratic_expansion.

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

theorem reciprocal_base_denominator_quadratic_expansion_sharp :
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
        E * z ^ (-(1 / 3 : ℝ))) := by sorry

end PrimePairSieve
