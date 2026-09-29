-- Prove2me | Theorems.Thm_RamareAnalytic_coefficient_logarithmic_moment
-- name    : RamareAnalytic.coefficient_logarithmic_moment
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-19T21:23:04.435578+00:00
-- url     : https://prove2.me/theorems/389119bf-7395-4a1c-a081-42712c1736bd
-- title:
--   Exact logarithmic moment of Ramaré’s multiplicative correction
-- statement:
--   Let $h$ be a real multiplicative arithmetic function with
--
--   $$h(p)=\frac1{p(p-1)},\qquad h(p^2)=-\frac1{p(p-1)},\qquad h(p^k)=0\quad(k\ge3)$$
--
--   for every prime $p$. Then the prime series converges unconditionally and its sum is the negative logarithmic moment of $h$:
--
--   $$\sum_{p\text{ prime}}\frac{\log p}{p(p-1)}=-\sum_{n\ge0}h(n)\log n.$$
--
--   Convergence of the coefficient moments is derived from the prime-power values, not assumed. The proof first identifies the logarithmic moment on numbers supported by each finite set of primes, and then passes to the limit using absolute convergence. It does not differentiate an infinite Euler product. Arithmetic functions vanish at zero; the zero-index logarithmic term consequently vanishes under the library's totalized logarithm convention.
--
--   This identity supplies the center of the harmonic-convolution asymptotic for the squarefree reciprocal-totient sum. Numerical estimates for that center and the weighted error moment are separate obligations.
-- source:
--   O. Ramaré, On Shnirelman's constant, Ann. Scuola Norm. Sup. Pisa 22 (1995), 645–706, printed pp. 656–660, harmonic convolution and correction Euler factors. https://www.numdam.org/item/ASNSP_1995_4_22_4_645_0/ . This development's correction coefficients and convergence theorem are https://prove2.me/theorems/a866384b-78aa-46c7-90df-9bbecf5707a5 and https://prove2.me/theorems/7395dd2e-3172-4af5-8d16-8debb89e26ed . The harmonic-error consumer is https://prove2.me/theorems/c5e5cedf-d538-4888-b726-db041653e0b7 .

import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
set_option autoImplicit false
open scoped BigOperators

theorem RamareAnalytic.coefficient_logarithmic_moment
    (h : ArithmeticFunction ℝ) (hmul : h.IsMultiplicative)
    (hpv : ∀ p : ℕ, Nat.Prime p →
      h p = 1 / ((p : ℝ) * ((p : ℝ) - 1)) ∧
      h (p ^ 2) = -(1 / ((p : ℝ) * ((p : ℝ) - 1))))
    (hpz : ∀ p k : ℕ, Nat.Prime p → 3 ≤ k → h (p ^ k) = 0) :
    HasSum (fun p : Nat.Primes =>
      Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)))
      (-(∑' n : ℕ, h n * Real.log (n : ℝ))) := by sorry
