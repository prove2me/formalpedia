-- Prove2me | Theorems.Thm_PrimePairSieve_reciprocal_base_denominator_quadratic_expansion
-- name    : PrimePairSieve.reciprocal_base_denominator_quadratic_expansion
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-20T01:24:23.002084+00:00
-- url     : https://prove2.me/theorems/0cde8aa6-fbd7-4102-b02d-fd41125cdfc7
-- title:
--   Quadratic expansion of the reciprocal-weighted base sieve denominator
-- statement:
--   For $z>0$, define the reciprocal-weighted base sieve denominator
--
--   $$S_2(z)=\sum_{1\le n\le z}\frac{b(n)}{1+n/z},\qquad
--   b(n)=\mathbf1_{\mathrm{squarefree}(n)}\prod_{p\mid n}b_p,
--   \qquad b_2=1,\quad b_p=\frac2{p-2}\ (p>2).$$
--
--   Let $\gamma$ be the Euler–Mascheroni constant and put
--
--   $$A=\sum_{p\text{ prime}}\frac{\log p}{p(p-1)},\qquad
--   C=2\inf_{Q\in\mathbb N}\prod_{\substack{2<p\le Q\\p\text{ prime}}}
--   \left(1-\frac1{(p-1)^2}\right).$$
--
--   There exist real constants $B$ and $E\ge0$, fixed independently of $z$, such that every $z>0$ satisfies
--
--   $$\left|S_2(z)-
--   \frac{\log^2z+(4\gamma+4A-\log2)\log z+B}{2C}\right|
--   \le E z^{-1/3}.$$
--
--   The sum uses the natural floor of the real cutoff and is empty for $0<z<1$. This fixes the two leading logarithmic coefficients with one error constant for all positive real cutoffs. No numerical value of $B$, numerical upper bound on $E$, effective cutoff, or prime-pair counting bound is asserted.
-- source:
--   H. Riesel and R. C. Vaughan, On sums of primes, Arkiv för Matematik 21 (1983), 45–74. The reciprocal weight is equation (3.12), printed p.51; the Abel identity on printed p.52 immediately before (3.15) transfers the base denominator expansion to this weight. https://archive.ymsc.tsinghua.edu.cn/pacm_download/116/7384-11512_2006_Article_BF02384300.pdf . This is a formalization of known mathematics with existential finite constants, not a novelty claim or the paper's sharper numerical remainder. It reuses the accepted PrimePairSieve.base_denominator_quadratic_expansion, https://prove2.me/theorems/939b1b68-fc27-4e1e-9ec6-12514ea6b076 . Intended mission consumer: TaoFivePrimes.siebert_prime_pair_bound, https://prove2.me/theorems/0b3aa912-642f-4b13-b915-0b43c7e7c385 .

import Definitions.Def_TaoFivePrimes_SingularSeries
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.SpecialFunctions.Pow.Real
set_option autoImplicit false
open scoped BigOperators

theorem PrimePairSieve.reciprocal_base_denominator_quadratic_expansion :
    ∃ B E : ℝ, 0 ≤ E ∧ ∀ z : ℝ, 0 < z →
      |(∑ n ∈ Finset.Icc 1 ⌊z⌋₊,
          (if Squarefree n then
            ∏ p ∈ n.primeFactors, if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)
          else 0) / (1 + (n : ℝ) / z)) -
        (Real.log z ^ 2 +
          (4 * Real.eulerMascheroniConstant +
            4 * (∑' p : Nat.Primes,
              Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) - Real.log 2) *
            Real.log z + B) / (2 * TaoFivePrimes.twinPrimeConstant)| ≤
        E * z ^ (-(1 / 3 : ℝ)) := by sorry
