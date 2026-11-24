-- Prove2me | Theorems.Thm_PrimePairSieve_base_correction_summability_and_mass
-- name    : PrimePairSieve.base_correction_summability_and_mass
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-19T23:42:19.446984+00:00
-- url     : https://prove2.me/theorems/95419970-893c-451e-b468-afc8659164da
-- title:
--   Weighted summability and exact mass of the base prime-pair sieve correction
-- statement:
--   For each prime $p$, set
--
--   $$b_p=\begin{cases}1,&p=2,\\2/(p-2),&p>2.\end{cases}$$
--
--   Let $h:\mathbb N\to\mathbb R$ be a multiplicative arithmetic function, vanishing at zero and with $h(1)=1$. Suppose its prime-power values satisfy
--
--   $$h(p)=b_p-\frac2p,\qquad
--   h(p^2)=\frac1{p^2}-\frac{2b_p}{p},\qquad
--   h(p^3)=\frac{b_p}{p^2},\qquad
--   h(p^j)=0\quad(j\ge4).$$
--
--   Then the weighted absolute series converges and the signed coefficient mass is exactly
--
--   $$\sum_{n\ge1}|h(n)|n^{2/5}<\infty,
--   \qquad \sum_{n\ge1}h(n)=\frac1C,$$
--
--   where $C$ is the existing public twin-prime constant with its precise definition
--
--   $$C=2\inf_{Q\in\mathbb N}\prod_{\substack{p\le Q\\p\text{ prime},\ p>2}}
--   \left(1-\frac1{(p-1)^2}\right).$$
--
--   Convergence is a conclusion, not an assumption. The same coefficients occur in the exact double-harmonic convolution of the base-shift-two prime-pair sieve denominator; the exceptional values are $h(2)=0$, $h(4)=-3/4$, and $h(8)=1/4$. This result identifies its leading coefficient and provides qualitative moment control. It asserts no numerical bound on the weighted sum and no complete prime-pair counting estimate.
-- source:
--   H. Riesel and R. C. Vaughan, On sums of primes, Arkiv för Matematik 21 (1983), 45–74. Coefficients and absolute Euler series: (2.5)–(2.7), printed p.46; convergence region and double-harmonic convolution: (3.3)–(3.5), p.50; reciprocal mass: (3.9), p.50. https://archive.ymsc.tsinghua.edu.cn/pacm_download/116/7384-11512_2006_Article_BF02384300.pdf . Their correction g is denoted h here. The exponent 2/5 and coarse finite-factor majorants are auxiliary choices within the classical convergence region; no novelty claim. Uses the actual public TaoFivePrimes.twinPrimeConstant definition. Coefficient consumer: PrimePairSieve.exists_base_double_harmonic_coefficients, https://prove2.me/theorems/189ed5bc-9d5d-4499-bdf0-76b3f2d9bea0 . Mission consumer: TaoFivePrimes.siebert_prime_pair_bound, https://prove2.me/theorems/0b3aa912-642f-4b13-b915-0b43c7e7c385 .

import Definitions.Def_TaoFivePrimes_SingularSeries
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
set_option autoImplicit false
open scoped BigOperators

theorem PrimePairSieve.base_correction_summability_and_mass (h : ArithmeticFunction ℝ) (hmul : h.IsMultiplicative)
    (hpv : ∀ p : ℕ, Nat.Prime p →
      h p = (if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) - 2 / (p : ℝ) ∧
      h (p ^ 2) = 1 / (p : ℝ)^2 -
        2 * (if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) / (p : ℝ) ∧
      h (p ^ 3) =
        (if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) / (p : ℝ)^2)
    (hpz : ∀ p k : ℕ, Nat.Prime p → 4 ≤ k → h (p ^ k) = 0) :
    Summable (fun n : ℕ => |h n| * (n : ℝ) ^ (2 / 5 : ℝ)) ∧
      HasSum (fun n : ℕ => h n) (1 / TaoFivePrimes.twinPrimeConstant) := by sorry
