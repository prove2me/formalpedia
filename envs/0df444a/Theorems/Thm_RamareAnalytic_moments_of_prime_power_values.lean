-- Prove2me | Theorems.Thm_RamareAnalytic_moments_of_prime_power_values
-- name    : RamareAnalytic.moments_of_prime_power_values
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-19T21:02:58.289984+00:00
-- url     : https://prove2.me/theorems/7395dd2e-3172-4af5-8d16-8debb89e26ed
-- title:
--   Convergent moments and total mass of Ramaré’s multiplicative correction
-- statement:
--   Let $h:\mathbb N\to\mathbb R$ be a multiplicative arithmetic function, so $h(0)=0$, $h(1)=1$, and $h(mn)=h(m)h(n)$ whenever $m,n$ are coprime. Suppose that for every prime $p$,
--
--   $$h(p)=\frac1{p(p-1)},\qquad h(p^2)=-\frac1{p(p-1)},\qquad h(p^k)=0\quad(k\ge3).$$
--
--   Then the coefficient series has total mass one, and its logarithmic and weighted absolute moments converge:
--
--   $$\sum_{n\ge0}h(n)=1,\qquad \sum_{n\ge0}h(n)\log n\text{ converges},\qquad \sum_{n\ge0}|h(n)|n^{2/5}<\infty.$$
--
--   All infinite sums use unconditional convergence; the logarithmic moment is therefore absolutely convergent over the real numbers. The zero-index terms vanish, with the real logarithm totalized at zero as in the formal library.
--
--   These are the qualitative convergence and normalization inputs needed to apply the harmonic-convolution error theorem to the squarefree reciprocal-totient weight. The prime-power values are the assumptions; convergence and total mass are conclusions. The theorem does not give the numerical bounds on the two moments required by the final large-range estimate.
-- source:
--   O. Ramaré, On Shnirelman's constant, Ann. Scuola Norm. Sup. Pisa22 (1995),645–706, harmonic-convolution method and correction Euler factors, printed pp.656–660, especially equations(3.7)–(3.8). https://www.numdam.org/item/ASNSP_1995_4_22_4_645_0/ . The weighted exponent2/5 is an auxiliary choice of this formal development, not a verbatim claim from the paper. The explicit coefficient existence/finite convolution is https://prove2.me/theorems/a866384b-78aa-46c7-90df-9bbecf5707a5 ; the error-transfer consumer is https://prove2.me/theorems/c5e5cedf-d538-4888-b726-db041653e0b7 .

import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
set_option autoImplicit false

theorem RamareAnalytic.moments_of_prime_power_values
    (h : ArithmeticFunction ℝ) (hmul : h.IsMultiplicative)
    (hpv : ∀ p : ℕ, Nat.Prime p →
      h p = 1 / ((p : ℝ) * ((p : ℝ) - 1)) ∧
      h (p ^ 2) = -(1 / ((p : ℝ) * ((p : ℝ) - 1))))
    (hpz : ∀ p k : ℕ, Nat.Prime p → 3 ≤ k → h (p ^ k) = 0) :
    HasSum (fun n : ℕ => h n) 1 ∧
      Summable (fun n : ℕ => h n * Real.log (n : ℝ)) ∧
      Summable (fun n : ℕ => |h n| * (n : ℝ) ^ (2 / 5 : ℝ)) := by sorry
