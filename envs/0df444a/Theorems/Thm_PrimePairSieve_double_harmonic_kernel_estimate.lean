-- Prove2me | Theorems.Thm_PrimePairSieve_double_harmonic_kernel_estimate
-- name    : PrimePairSieve.double_harmonic_kernel_estimate
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-19T23:45:37.331501+00:00
-- url     : https://prove2.me/theorems/70030375-ee1e-4e93-9840-5534462bdb6a
-- title:
--   A common Stieltjes constant and an explicit double-harmonic kernel estimate
-- statement:
--   There is one real constant $c$ such that
--
--   $$c=\lim_{n\to\infty}\left(\sum_{a=1}^n\frac{\log a}{a}-\frac12\log^2n\right),$$
--
--   and, for every natural $n\ge3$,
--
--   $$0\le\sum_{a=1}^n\frac{\log a}{a}-\frac12\log^2n-c\le\frac{\log n}{n}.$$
--
--   For the same constant, every natural $N\ge9$ satisfies, with $m=\lfloor\sqrt N\rfloor$,
--
--   $$\left|\sum_{a=1}^N\frac{H_{\lfloor N/a\rfloor}}a-
--   \left(\frac12\log^2N+2\gamma\log N+\gamma^2-2c\right)\right|
--   \le\frac3{m^2}+\frac{2\log N}{m}+\frac{4m}{N}.$$
--
--   Here $H_j=\sum_{i=1}^j1/i$, $H_0=0$, all logarithms are natural, and $\gamma$ is the Euler–Mascheroni constant. The limit identifies $c$ as the first Stieltjes constant in the log-weighted-sum convention; its numerical value is not assumed. This is a quantitative estimate for the double-harmonic kernel appearing in the dimension-two sieve convolution, independent of any correction coefficient or moment bound. The cutoff is natural, and the displayed error is an elementary alternative to the sharper uniform error in the cited source.
-- source:
--   H. Riesel and R. C. Vaughan, On sums of primes, Arkiv för Matematik 21 (1983), 45–74: equation (2.1), printed p.45, defines the constant convention; Lemma 1 and equation (3.1), printed p.48, give the double-harmonic/divisor kernel centre and the square-root hyperbola identity; equation (3.5), printed p.50, gives its sieve-convolution use. https://archive.ymsc.tsinghua.edu.cn/pacm_download/116/7384-11512_2006_Article_BF02384300.pdf . The present explicit error is derived from elementary monotone integral comparisons and harmonic bounds, and does not assert the paper's stronger 1.641*x^(-1/3) remainder. No novelty claim. Intended consumer: PrimePairSieve.exists_base_double_harmonic_coefficients, then TaoFivePrimes.siebert_prime_pair_bound https://prove2.me/theorems/0b3aa912-642f-4b13-b915-0b43c7e7c385 .

import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Data.Nat.Sqrt
set_option autoImplicit false
open scoped BigOperators Topology

theorem PrimePairSieve.double_harmonic_kernel_estimate :
    ∃ c : ℝ,
      Filter.Tendsto
        (fun n : ℕ =>
          (∑ a ∈ Finset.Icc 1 n, Real.log (a : ℝ) / (a : ℝ)) -
            Real.log (n : ℝ)^2 / 2)
        Filter.atTop (𝓝 c) ∧
      (∀ n : ℕ, 3 ≤ n →
        0 ≤ (∑ a ∈ Finset.Icc 1 n, Real.log (a : ℝ) / (a : ℝ)) -
          Real.log (n : ℝ)^2 / 2 - c ∧
        (∑ a ∈ Finset.Icc 1 n, Real.log (a : ℝ) / (a : ℝ)) -
          Real.log (n : ℝ)^2 / 2 - c ≤ Real.log (n : ℝ) / (n : ℝ)) ∧
      (∀ N : ℕ, 9 ≤ N →
        |(∑ a ∈ Finset.Icc 1 N, (harmonic (N / a) : ℝ) / (a : ℝ)) -
          (Real.log (N : ℝ)^2 / 2 +
            2 * Real.eulerMascheroniConstant * Real.log (N : ℝ) +
            Real.eulerMascheroniConstant^2 - 2 * c)| ≤
          3 / (Nat.sqrt N : ℝ)^2 +
            2 * Real.log (N : ℝ) / (Nat.sqrt N : ℝ) +
            4 * (Nat.sqrt N : ℝ) / (N : ℝ)) := by sorry
