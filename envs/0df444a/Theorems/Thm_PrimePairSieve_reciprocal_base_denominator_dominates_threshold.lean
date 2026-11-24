-- Prove2me | Theorems.Thm_PrimePairSieve_reciprocal_base_denominator_dominates_threshold
-- name    : PrimePairSieve.reciprocal_base_denominator_dominates_threshold
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-23T13:34:24.978259+00:00
-- url     : https://prove2.me/theorems/dd059254-26a3-414d-be7b-44976fbe068b
-- title:
--   The reciprocal base denominator dominates the sieve threshold from z = 40
-- statement:
--   ## Statement
--
--   Let
--   $$B(z)=\sum_{\substack{q\le z\\ q\ \mathrm{squarefree}}}\ \frac{\prod_{p\mid q} b_p}{1+q/z},
--   \qquad b_2=1,\qquad b_p=\frac{2}{p-2}\ (p>2),$$
--   let $C$ be the twin-prime singular constant, and for $z\ge 40$ put
--   $$T(z)=\frac{\log^2(4z)}{2C},\qquad
--   T_{\mathrm{req}}(z)=\frac{T(z)}{1-\dfrac{(z+1)\,T(z)}{16z^2}}.$$
--
--   The theorem states that for every real $z\ge 40$
--   $$T_{\mathrm{req}}(z)\ \le\ B(z).$$
--
--   ## Meaning
--
--   This is the endgame comparison for the large-$x$ route to `TaoFivePrimes.siebert_prime_pair_bound`. In that reduction, the sieve bound `PrimePairSieve_prime_pair_count_base_reciprocal_bound` gives, for $x\ge 16$ and $z=\sqrt x/4$,
--   $$\#\{\text{prime pairs with gap } d\text{ up to }x\}\ \le\ K(d)\,\frac{x}{B(z)}+z+1 ,$$
--   so it suffices to know that $B(z)$ dominates the threshold $T_{\mathrm{req}}(z)$: the mild factor $1/(1-(z+1)T/x)$ in $T_{\mathrm{req}}$ is exactly what absorbs the additive term $z+1$ of the sieve bound (using $x=16z^2$ and $K(d)\ge1$), and then $Kx/T_{\mathrm{req}}+(z+1)\le Kx/T=8CKx/\log^2 x$, which is the target expression.
--
--   The threshold first becomes approachable at $z=40$: at $z=40$ the worst-case margin obtained from the sharp reciprocal expansion ($E\le10/3$, expansion constant $B\ge-\tfrac32$, worst case combined) is $T_{\mathrm{req}}(40)/(1-\ldots)$ … more precisely $B(40)-T_{\mathrm{req}}(40)\ge 0.17$ in these normalizations, and the difference is increasing in $z$ on $[40,\infty)$; with the true (not worst-case) error constant $E\approx1.97$ the margin is $\ge1.19$ already, and grows like $\tfrac{1.86}{2C}\log z$.
--
--   ## Route
--
--   Provable from `PrimePairSieve.reciprocal_base_denominator_quadratic_expansion_sharp` by a purely elementary comparison: with $L=\log z$,
--   $$B(z)\ \ge\ \frac{L^2+(4\gamma+4P-\log2)L-\tfrac32}{2C}-\frac{10}{3}z^{-1/3},$$
--   and, after multiplying by $2C$, the required inequality becomes
--   $$L^2+(4\gamma+4P-\log 2)L-\tfrac32-\frac{20C}{3}z^{-1/3}\ \ge\ \frac{(L+\log4)^2}{1-(z+1)(L+\log4)^2/(32Cz^2)} .$$
--   The left side minus the right side equals $1.8645\ldots L-3.42\ldots-\frac{20C}{3}z^{-1/3}-\frac{1.04\,(z+1)(L+\log4)^4}{32Cz^2}$, which is increasing for $z\ge40$ (the last term is decreasing there because $(\log 4z)\,(z+2)\ge4(z+1)$, a consequence of $\log4z\ge5$) and positive at $z=40$ once the constants are certified to a few decimals: $4\gamma+4P-\log2\in[4.637,4.638]$, $C\in[1.320,1.321]$, $\log40\in[3.688,3.689]$, $\log160\in[5.075,5.076]$. All these bounds are provable by the same certificate-style finite computations used elsewhere in this project.
--
--   ## Reference
--
--   Endgame step for `TaoFivePrimes.siebert_prime_pair_bound`; compare H. Riesel and R. C. Vaughan, *On sums of primes*, Ark. Mat. **21** (1983), 46--74.
-- source:
--   Endgame comparison for TaoFivePrimes.siebert_prime_pair_bound; Riesel-Vaughan base denominator expansion.

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

theorem reciprocal_base_denominator_dominates_threshold :
    ∀ z : ℝ, 40 ≤ z →
      (Real.log (4 * z)) ^ 2 / (2 * TaoFivePrimes.twinPrimeConstant) /
          (1 - ((z + 1) * ((Real.log (4 * z)) ^ 2 /
            (2 * TaoFivePrimes.twinPrimeConstant)) / (16 * z ^ 2)))
        ≤ ∑ q ∈ Finset.Icc 1 ⌊z⌋₊,
          (if Squarefree q then
            ∏ p ∈ q.primeFactors, if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)
          else 0) / (1 + (q : ℝ) / z) := by sorry

end PrimePairSieve
