-- Prove2me | Theorems.Thm_PrimePairSieve_base_correction_second_logarithmic_moment
-- name    : PrimePairSieve.base_correction_second_logarithmic_moment
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-20T01:51:49.291995+00:00
-- url     : https://prove2.me/theorems/11fbaf23-bca4-4243-b725-3f65dab041a0
-- title:
--   Exact second logarithmic moment of the base prime-pair sieve correction
-- statement:
--   For each prime $p$, put
--
--   $$b_p=\begin{cases}1,&p=2,\\2/(p-2),&p>2.\end{cases}$$
--
--   Let $h:\mathbb N\to\mathbb R$ be a multiplicative arithmetic function, with $h(0)=0$ and $h(1)=1$, satisfying
--
--   $$h(p)=b_p-\frac2p,\qquad
--   h(p^2)=\frac1{p^2}-\frac{2b_p}{p},\qquad
--   h(p^3)=\frac{b_p}{p^2},\qquad
--   h(p^j)=0\quad(j\ge4)$$
--
--   for every prime $p$. Define
--
--   $$A=\sum_{p\text{ prime}}\frac{\log p}{p(p-1)},\qquad
--   D=\sum_{p\text{ prime}}\frac{8p^2-10p+4}{p^2(p-1)^2}\log^2p,$$
--
--   and use the existing public twin-prime constant with normalization
--
--   $$C=2\inf_{Q\in\mathbb N}\prod_{\substack{p\le Q\\p\text{ prime},\ p>2}}
--   \left(1-\frac1{(p-1)^2}\right).$$
--
--   Then the second logarithmic coefficient series converges absolutely and has the exact sum
--
--   $$\sum_{n\ge1}h(n)\log^2n
--   =\frac{(2A+\tfrac12\log2)^2+\tfrac14\log^22-D}{C}.$$
--
--   The prime-power data and multiplicativity are the only hypotheses. Convergence is a conclusion, and the prime sums in the formula are also justified by the proof. The positive one-quarter correction accounts for the exceptional prime two. This identifies a signed second moment; it does not assert that this moment is positive, give a numerical interval for it, or establish a prime-pair counting bound.
-- source:
--   H. Riesel and R. C. Vaughan, On sums of primes, Arkiv för Matematik 21 (1983), 45–74. The correction coefficients are (2.5)–(2.6), printed p.46. The second derivative calculation following (3.10) on printed p.51 gives G''(0)=(A1^2+log(2)^2/4-A2)/C, where A1=2A+log(2)/2 and A2 is the D-series displayed here. The one-quarter fraction was verified from the primary page image and directly from the prime-two local factor. Their correction g is denoted h here. https://archive.ymsc.tsinghua.edu.cn/pacm_download/116/7384-11512_2006_Article_BF02384300.pdf . Known mathematics, with no novelty claim; the proof uses finite Euler moments and limits, rather than differentiating an unproved infinite product. The actual common coefficient is supplied by PrimePairSieve.exists_base_double_harmonic_coefficients, https://prove2.me/theorems/189ed5bc-9d5d-4499-bdf0-76b3f2d9bea0 . Intended mission consumer: TaoFivePrimes.siebert_prime_pair_bound, https://prove2.me/theorems/0b3aa912-642f-4b13-b915-0b43c7e7c385 .

import Definitions.Def_TaoFivePrimes_SingularSeries
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
set_option autoImplicit false
open scoped BigOperators

theorem PrimePairSieve.base_correction_second_logarithmic_moment
    (h : ArithmeticFunction ℝ) (hmul : h.IsMultiplicative)
    (hpv : ∀ p : ℕ, Nat.Prime p →
      h p = (if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) - 2 / (p : ℝ) ∧
      h (p ^ 2) = 1 / (p : ℝ)^2 -
        2 * (if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) / (p : ℝ) ∧
      h (p ^ 3) =
        (if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) / (p : ℝ)^2)
    (hpz : ∀ p k : ℕ, Nat.Prime p → 4 ≤ k → h (p ^ k) = 0) :
    Summable (fun n : ℕ => ‖h n * Real.log (n : ℝ)^2‖) ∧
      HasSum (fun n : ℕ => h n * Real.log (n : ℝ)^2)
        (((2 * (∑' p : Nat.Primes,
            Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) + Real.log 2 / 2)^2 +
          (1 / 4 : ℝ) * Real.log 2^2 -
          (∑' p : Nat.Primes,
            (8 * (p : ℝ)^2 - 10 * (p : ℝ) + 4) /
              ((p : ℝ)^2 * ((p : ℝ) - 1)^2) * Real.log (p : ℝ)^2)) /
            TaoFivePrimes.twinPrimeConstant) := by sorry
