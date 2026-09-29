-- Prove2me | Theorems.Thm_PrimePairSieve_exists_base_double_harmonic_coefficients
-- name    : PrimePairSieve.exists_base_double_harmonic_coefficients
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-19T23:13:43.729982+00:00
-- url     : https://prove2.me/theorems/189ed5bc-9d5d-4499-bdf0-76b3f2d9bea0
-- title:
--   Multiplicative double-harmonic coefficients for the base prime-pair sieve sum
-- statement:
--   For every prime $p$, put
--
--   $$b_p=\begin{cases}1,&p=2,\\2/(p-2),&p>2.\end{cases}$$
--
--   There is one multiplicative arithmetic function $h:\mathbb N\to\mathbb R$, with $h(0)=0$ and $h(1)=1$, satisfying
--
--   $$h(p)=b_p-\frac2p,\qquad
--   h(p^2)=\frac1{p^2}-\frac{2b_p}{p},\qquad
--   h(p^3)=\frac{b_p}{p^2},\qquad
--   h(p^j)=0\quad(j\ge4)$$
--
--   at every prime, and the following identity at every natural cutoff $N$, including zero:
--
--   $$\sum_{n=1}^{N}\mathbf1_{\mathrm{Squarefree}(n)}\prod_{p\mid n}b_p
--   =\sum_{d=1}^{N}h(d)\sum_{a=1}^{\lfloor N/d\rfloor}
--   \frac{H_{\lfloor N/(da)\rfloor}}a.$$
--
--   Here products are over distinct prime factors, $H_m=\sum_{j=1}^{m}1/j$, and $H_0=0$. Multiplicativity means $h(mn)=h(m)h(n)$ for coprime $m,n$. The same function satisfies every prime-power formula and every cutoff identity.
--
--   The left side is the sharp-cutoff base-shift-two Selberg denominator. In particular $(h(2),h(4),h(8))=(0,-3/4,1/4)$; the exceptional prime two is included. This statement supplies the finite algebraic input to a dimension-two convolution estimate. It makes no assertion of convergence, coefficient mass, logarithmic moments, a denominator lower bound, or the all-range prime-pair inequality.
-- source:
--   H. Riesel and R. C. Vaughan, On sums of primes, Arkiv för Matematik 21 (1983), 45–74. Correction coefficients: equations (2.5)–(2.6), printed p.46; exact double-harmonic convolution: equation (3.5), printed p.50, in the proof of Lemma 2. https://archive.ymsc.tsinghua.edu.cn/pacm_download/116/7384-11512_2006_Article_BF02384300.pdf . Their correction is denoted g; the present statement calls it h. This is a finite formalization of known mathematics, with no novelty claim. Intended consumer: TaoFivePrimes.siebert_prime_pair_bound https://prove2.me/theorems/0b3aa912-642f-4b13-b915-0b43c7e7c385 .

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Harmonic.Bounds
set_option autoImplicit false
open scoped BigOperators

theorem PrimePairSieve.exists_base_double_harmonic_coefficients :
    ∃ h : ArithmeticFunction ℝ, h.IsMultiplicative ∧
    (∀ p : ℕ, Nat.Prime p →
      h p = (if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) - 2 / (p : ℝ) ∧
      h (p ^ 2) = 1 / (p : ℝ)^2 -
        2 * (if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) / (p : ℝ) ∧
      h (p ^ 3) =
        (if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) / (p : ℝ)^2) ∧
    (∀ p k : ℕ, Nat.Prime p → 4 ≤ k → h (p ^ k) = 0) ∧
    (∀ N : ℕ,
      (∑ n ∈ Finset.Icc 1 N,
        if Squarefree n then
          ∏ p ∈ n.primeFactors, if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)
        else 0) =
      ∑ d ∈ Finset.Icc 1 N, h d *
        ∑ a ∈ Finset.Icc 1 (N / d), (harmonic ((N / d) / a) : ℝ) / (a : ℝ)) := by sorry
