-- Prove2me | Theorems.Thm_PrimePairSieve_base_denominator_quadratic_expansion
-- name    : PrimePairSieve.base_denominator_quadratic_expansion
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-20T00:25:56.178053+00:00
-- url     : https://prove2.me/theorems/939b1b68-fc27-4e1e-9ec6-12514ea6b076
-- title:
--   Quadratic logarithmic expansion of the base prime-pair sieve denominator
-- statement:
--   For each positive real $z$, define the base dimension-two sieve denominator
--
--   $$S(z)=\sum_{1\le n\le z}\mu^2(n)\prod_{p\mid n}b_p,
--   \qquad b_2=1,\quad b_p=\frac2{p-2}\ (p>2).$$
--
--   Here $\mu^2$ is the squarefree indicator. Let $\gamma$ be the Euler–Mascheroni constant, put
--
--   $$A=\sum_{p\text{ prime}}\frac{\log p}{p(p-1)},\qquad
--   C=2\inf_{Q\in\mathbb N}\prod_{\substack{2<p\le Q\\p\text{ prime}}}
--   \left(1-\frac1{(p-1)^2}\right),$$
--
--   and use this precise normalization of the twin-prime constant. There exist real constants $B$ and $E\ge0$, fixed independently of $z$, such that every $z>0$ satisfies
--
--   $$\left|S(z)-\frac{\log^2z+(4\gamma+4A+\log2)\log z+B}{2C}\right|
--   \le E z^{-1/3}.$$
--
--   This determines both leading coefficients and gives a decaying error with one common constant over all positive real cutoffs, including noninteger cutoffs and the empty-sum regime $0<z<1$. The constants are constructed from convergent coefficient moments. No numerical value of $B$ or upper bound on $E$ is asserted. This is a denominator estimate; the weighted sieve inequality and a bound for the prime-pair count are separate statements.
-- source:
--   H. Riesel and R. C. Vaughan, On sums of primes, Arkiv för Matematik21 (1983),45–74, equations (3.2)–(3.11), printed pp.50–51; Lemma1, pp.48–50. https://archive.ymsc.tsinghua.edu.cn/pacm_download/116/7384-11512_2006_Article_BF02384300.pdf . This records the classical expansion with existential finite constants and a coarser proved kernel remainder; it does not claim the source's numerical1.641 error coefficient. Uses the actual public TaoFivePrimes.twinPrimeConstant. Intended downstream consumer: TaoFivePrimes.siebert_prime_pair_bound, https://prove2.me/theorems/0b3aa912-642f-4b13-b915-0b43c7e7c385 .

import Definitions.Def_TaoFivePrimes_SingularSeries
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.SpecialFunctions.Pow.Real
set_option autoImplicit false
open scoped BigOperators

theorem PrimePairSieve.base_denominator_quadratic_expansion :
    ∃ B E : ℝ, 0 ≤ E ∧ ∀ z : ℝ, 0 < z →
      |(∑ n ∈ Finset.Icc 1 ⌊z⌋₊,
          if Squarefree n then
            ∏ p ∈ n.primeFactors, if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)
          else 0) -
        (Real.log z ^ 2 +
          (4 * Real.eulerMascheroniConstant +
            4 * (∑' p : Nat.Primes,
              Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) + Real.log 2) *
            Real.log z + B) / (2 * TaoFivePrimes.twinPrimeConstant)| ≤
        E * z ^ (-(1 / 3 : ℝ)) := by sorry
