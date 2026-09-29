-- Prove2me | Theorems.Thm_PrimePairSieve_base_correction_one_third_moment_bound
-- name    : PrimePairSieve.base_correction_one_third_moment_bound
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-20T01:31:29.394981+00:00
-- url     : https://prove2.me/theorems/d550d493-ff11-43a4-88cf-293d4467349b
-- title:
--   Explicit one-third absolute moment bound for the base prime-pair sieve correction
-- statement:
--   For each prime $p$, write
--
--   $$b_p=\begin{cases}1,&p=2,\\2/(p-2),&p>2.\end{cases}$$
--
--   Let $h:\mathbb N\to\mathbb R$ be a multiplicative arithmetic function with $h(0)=0$ and $h(1)=1$, satisfying
--
--   $$h(p)=b_p-\frac2p,\qquad
--   h(p^2)=\frac1{p^2}-\frac{2b_p}{p},\qquad
--   h(p^3)=\frac{b_p}{p^2},\qquad
--   h(p^j)=0\quad(j\ge4).$$
--
--   Then its one-third weighted absolute series converges, and
--
--   $$W_{1/3}:=\sum_{n\ge1}|h(n)|n^{1/3}
--   \le\frac{7491}{25}<300.$$
--
--   In particular the exceptional prime values are $h(2)=0$, $h(4)=-3/4$, and $h(8)=1/4$. Convergence and the numerical bound are conclusions; there is no assumed Euler-product, finite-product, or prime-tail estimate. These are the coefficients in the base prime-pair sieve's double-harmonic convolution. The bound is deliberately coarser than the source's $251.0128$ estimate and supplies quantitative error control, rather than a complete prime-pair counting theorem.
-- source:
--   H. Riesel and R. C. Vaughan, On sums of primes, Arkiv för Matematik 21 (1983), 45–74. The multiplicative coefficients, absolute Dirichlet series and sharper one-third moment bounds are (2.5)–(2.8), printed p.46; finite-product and tail evaluation are discussed on pp.72–73. https://archive.ymsc.tsinghua.edu.cn/pacm_download/116/7384-11512_2006_Article_BF02384300.pdf . Their correction g is denoted h here. This formal statement uses the coarser bound 7491/25<300 from a finite certificate through 1000 and an explicit prime tail, not the paper’s sharper 251.0128 bound; no novelty claim. Existing coefficient consumer: PrimePairSieve.exists_base_double_harmonic_coefficients, https://prove2.me/theorems/189ed5bc-9d5d-4499-bdf0-76b3f2d9bea0 . Mission consumer: TaoFivePrimes.siebert_prime_pair_bound, https://prove2.me/theorems/0b3aa912-642f-4b13-b915-0b43c7e7c385 .

import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
set_option autoImplicit false
open scoped BigOperators

theorem PrimePairSieve.base_correction_one_third_moment_bound
    (h : ArithmeticFunction ℝ) (hmul : h.IsMultiplicative)
    (hpv : ∀ p : ℕ, Nat.Prime p →
      h p = (if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) - 2 / (p : ℝ) ∧
      h (p ^ 2) = 1 / (p : ℝ)^2 -
        2 * (if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) / (p : ℝ) ∧
      h (p ^ 3) =
        (if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) / (p : ℝ)^2)
    (hpz : ∀ p k : ℕ, Nat.Prime p → 4 ≤ k → h (p ^ k) = 0) :
    Summable (fun n : ℕ => |h n| * (n : ℝ)^(1 / 3 : ℝ)) ∧
      (∑' n : ℕ, |h n| * (n : ℝ)^(1 / 3 : ℝ)) ≤ (7491 / 25 : ℝ) ∧
      (∑' n : ℕ, |h n| * (n : ℝ)^(1 / 3 : ℝ)) < 300 := by sorry
