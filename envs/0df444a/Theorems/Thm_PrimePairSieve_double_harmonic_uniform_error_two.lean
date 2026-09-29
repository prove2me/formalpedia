-- Prove2me | Theorems.Thm_PrimePairSieve_double_harmonic_uniform_error_two
-- name    : PrimePairSieve.double_harmonic_uniform_error_two
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-20T01:06:53.96398+00:00
-- url     : https://prove2.me/theorems/c228f5db-5c94-4a2f-9a1c-d1de0381a4ef
-- title:
--   Uniform real-cutoff error bound for the double harmonic sum
-- statement:
--   Let $H_n=\sum_{a=1}^n1/a$ and let $\gamma$ be the Euler–Mascheroni constant. For every positive real $t$, put
--
--   $$K(t)=\sum_{1\le a\le t}\frac{H_{\lfloor t/a\rfloor}}a.
--   $$
--
--   There is one real constant $c\in[-1/6,0]$ satisfying
--
--   $$\lim_{N\to\infty}\left(\sum_{a=1}^N\frac{\log a}{a}-\frac12\log^2N\right)=c,
--   $$
--
--   such that every $t>0$ satisfies the explicit estimate
--
--   $$\left|K(t)-\left(\frac12\log^2t+2\gamma\log t+\gamma^2-2c\right)\right|
--   \le 2t^{-1/3}.
--   $$
--
--   The same constant appears in the limit and the kernel estimate. The estimate covers noninteger cutoffs and the empty-sum range $0<t<1$. This kernel controls the remainder when a dimension-two sieve denominator is written as a Dirichlet convolution with two reciprocal sequences. The coefficient $2$ is a coarser bound than the source's $1.641$; the latter is not asserted here.
-- source:
--   H. Riesel and R. C. Vaughan, On sums of primes, Arkiv för Matematik 21 (1983), 45–74, Lemma 1, printed pp. 48–50, with the logarithmically weighted harmonic limit in equation (2.1), p. 45. https://archive.ymsc.tsinghua.edu.cn/pacm_download/116/7384-11512_2006_Article_BF02384300.pdf . This is a coarser explicit remainder, not the source's numerical coefficient 1.641. Intended downstream use: the denominator estimate for TaoFivePrimes.siebert_prime_pair_bound.

import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.SpecialFunctions.Pow.Real
set_option autoImplicit false
open scoped BigOperators Topology

theorem PrimePairSieve.double_harmonic_uniform_error_two :
    ∃ c : ℝ, (-(1 / 6 : ℝ) ≤ c ∧ c ≤ 0) ∧
      Filter.Tendsto
        (fun n : ℕ =>
          (∑ a ∈ Finset.Icc 1 n, Real.log (a : ℝ) / (a : ℝ)) -
            Real.log (n : ℝ)^2 / 2)
        Filter.atTop (𝓝 c) ∧
      ∀ t : ℝ, 0 < t →
        |(∑ a ∈ Finset.Icc 1 ⌊t⌋₊,
            (harmonic (⌊t⌋₊ / a) : ℝ) / (a : ℝ)) -
          (Real.log t^2 / 2 + 2 * Real.eulerMascheroniConstant * Real.log t +
            Real.eulerMascheroniConstant^2 - 2 * c)| ≤
          2 * t ^ (-(1 / 3 : ℝ)) := by sorry
