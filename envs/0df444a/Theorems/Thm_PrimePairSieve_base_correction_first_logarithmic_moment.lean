-- Prove2me | Theorems.Thm_PrimePairSieve_base_correction_first_logarithmic_moment
-- name    : PrimePairSieve.base_correction_first_logarithmic_moment
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-20T00:09:49.213962+00:00
-- url     : https://prove2.me/theorems/bf399b48-f076-4f65-99b4-48ccbe38f472
-- title:
--   Exact first logarithmic moment of the base prime-pair sieve correction
-- statement:
--   For each prime $p$, set
--
--   $$b_p=\begin{cases}1,&p=2,\\2/(p-2),&p>2.\end{cases}$$
--
--   Let $h:\mathbb N\to\mathbb R$ be a multiplicative arithmetic function, with $h(0)=0$ and $h(1)=1$, such that
--
--   $$h(p)=b_p-\frac2p,\qquad
--   h(p^2)=\frac1{p^2}-\frac{2b_p}{p},\qquad
--   h(p^3)=\frac{b_p}{p^2},\qquad
--   h(p^j)=0\quad(j\ge4)$$
--
--   for every prime $p$. Write
--
--   $$A_0=\sum_{p\text{ prime}}\frac{\log p}{p(p-1)},\qquad
--   C=2\inf_{Q\in\mathbb N}\prod_{\substack{p\le Q\\p\text{ prime},\ p>2}}
--   \left(1-\frac1{(p-1)^2}\right).$$
--
--   Then the first logarithmic moment converges unconditionally and has the exact value
--
--   $$\sum_{n\ge1}h(n)\log n=-\frac{2A_0+\tfrac12\log2}{C}.$$
--
--   Here $C$ is the existing public twin-prime constant. The coefficient formulas include the exceptional values $h(2)=0$, $h(4)=-3/4$, and $h(8)=1/4$. The displayed prime-power values and multiplicativity are the only hypotheses; convergence of the coefficient moment is a conclusion. This is the first-moment identity for the correction used in the base prime-pair sieve convolution. It does not assert a second-moment value or a complete prime-pair counting bound.
-- source:
--   H. Riesel and R. C. Vaughan, On sums of primes, Arkiv för Matematik 21 (1983), 45–74. Correction coefficients: (2.5)–(2.6), printed p.46; A0 and A1=2A0+log(2)/2: (2.9)–(2.10), p.46; G(w)=sum g(n)n^(-w): (3.3), p.50; G'(0)=A1/C: (3.10), p.51. The coefficient logarithmic moment stated here is -G'(0), not G'(0); their g is denoted h here. https://archive.ymsc.tsinghua.edu.cn/pacm_download/116/7384-11512_2006_Article_BF02384300.pdf . Known source mathematics, with no novelty claim. Uses the actual public TaoFivePrimes.twinPrimeConstant definition. The same coefficient's existence and finite convolution are supplied by PrimePairSieve.exists_base_double_harmonic_coefficients, https://prove2.me/theorems/189ed5bc-9d5d-4499-bdf0-76b3f2d9bea0 . Intended mission consumer: TaoFivePrimes.siebert_prime_pair_bound, https://prove2.me/theorems/0b3aa912-642f-4b13-b915-0b43c7e7c385 .

import Definitions.Def_TaoFivePrimes_SingularSeries
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
set_option autoImplicit false
open scoped BigOperators

theorem PrimePairSieve.base_correction_first_logarithmic_moment
    (h : ArithmeticFunction ℝ) (hmul : h.IsMultiplicative)
    (hpv : ∀ p : ℕ, Nat.Prime p →
      h p = (if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) - 2 / (p : ℝ) ∧
      h (p ^ 2) = 1 / (p : ℝ)^2 -
        2 * (if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) / (p : ℝ) ∧
      h (p ^ 3) =
        (if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) / (p : ℝ)^2)
    (hpz : ∀ p k : ℕ, Nat.Prime p → 4 ≤ k → h (p ^ k) = 0) :
    HasSum (fun n : ℕ => h n * Real.log (n : ℝ))
      (-((2 * (∑' p : Nat.Primes,
        Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) + Real.log 2 / 2) /
          TaoFivePrimes.twinPrimeConstant)) := by sorry
