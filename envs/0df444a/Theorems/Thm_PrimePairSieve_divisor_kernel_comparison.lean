-- Prove2me | Theorems.Thm_PrimePairSieve_divisor_kernel_comparison
-- name    : PrimePairSieve.divisor_kernel_comparison
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-19T22:56:55.378767+00:00
-- url     : https://prove2.me/theorems/7bd2199f-5d3b-4077-9f98-c073bc638a1e
-- title:
--   Finite prime-pair sieve denominator comparison for antitone kernels
-- statement:
--   Let $P$ be squarefree and let $d$ be an even natural number. For each prime define
--
--   $$b_p=\begin{cases}1,&p=2,\\2/(p-2),&p>2,\end{cases}
--   \qquad
--    a_{d,p}=\begin{cases}1/(p-1),&p\mid d,\\2/(p-2),&p\nmid d.\end{cases}$$
--
--   For every nonincreasing function $F:\mathbb N\to\mathbb R$, the following finite comparison holds:
--
--   $$\sum_{n\mid P}\Bigl(\prod_{p\mid n}b_p\Bigr)F(n)
--   \le
--   \left[\prod_{\substack{p\mid P,\ p\mid d\\p>2}}\frac{p-1}{p-2}\right]
--   \sum_{n\mid P}\Bigl(\prod_{p\mid n}a_{d,p}\Bigr)F(n).$$
--
--   Products run over distinct prime factors. The statement permits $P=1$, $d=0$, and signed kernel values; no nonemptiness or $F\ge0$ assumption is needed. Evenness makes the prime-2 local coefficients equal, avoiding the exceptional denominator $p-2$ there. All coefficients, sums, and correction factors are written literally in the formal statement.
--
--   This finite comparison applies both to the sharp cutoff $F(n)=1_{n\le z}$ and, for $z>0$, to $F(n)=1_{n\le z}/(1+n/z)$. It separates the shift dependence of the prime-pair sieve denominator from the remaining analytic estimate for the base shift two. It does not assert that analytic estimate or the all-size Siebert bound.
-- source:
--   Classical finite sieve denominator comparison; weighted application: H. Riesel and R. C. Vaughan, On sums of primes, Arkiv för Matematik 21 (1983), 45–74, Lemma 3, equation (3.13), printed p.51. https://archive.ymsc.tsinghua.edu.cn/pacm_download/116/7384-11512_2006_Article_BF02384300.pdf . The present formal proof uses finite subset-product induction and Mathlib multiplicative prime-factor identities. Known mathematics; no novelty claim. Intended consumer: TaoFivePrimes.siebert_prime_pair_bound https://prove2.me/theorems/0b3aa912-642f-4b13-b915-0b43c7e7c385 .

import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Real.Basic
open scoped BigOperators
set_option autoImplicit false

theorem PrimePairSieve.divisor_kernel_comparison (P d : ℕ) (hP : Squarefree P) (hd : 2 ∣ d)
    (F : ℕ → ℝ) (hF : Antitone F) :
    (∑ n ∈ P.divisors,
      (∏ p ∈ n.primeFactors,
        if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) * F n) ≤
    (∑ n ∈ P.divisors,
      (∏ p ∈ n.primeFactors,
        if p ∣ d then (1 : ℝ) / ((p : ℝ) - 1) else 2 / ((p : ℝ) - 2)) * F n) *
      ∏ p ∈ P.primeFactors,
        if 2 < p ∧ p ∣ d then ((p : ℝ) - 1) / ((p : ℝ) - 2) else 1 := by sorry
