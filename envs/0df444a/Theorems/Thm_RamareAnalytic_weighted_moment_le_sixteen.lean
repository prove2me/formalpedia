-- Prove2me | Theorems.Thm_RamareAnalytic_weighted_moment_le_sixteen
-- name    : RamareAnalytic.weighted_moment_le_sixteen
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-19T21:32:17.380243+00:00
-- url     : https://prove2.me/theorems/77d81f35-58ed-4834-97d5-4eb9533d4ece
-- title:
--   Quantitative weighted moment of Ramaré’s multiplicative correction
-- statement:
--   Let $h$ be a real multiplicative arithmetic function such that, for every prime $p$,
--
--   $$h(p)=\frac1{p(p-1)},\qquad h(p^2)=-\frac1{p(p-1)},\qquad h(p^k)=0\quad(k\ge3).$$
--
--   Then its weighted absolute moment satisfies
--
--   $$\sum_{n\ge0}|h(n)|n^{2/5}\le16.$$
--
--   The same hypotheses guarantee convergence, as established by the companion correction-moment theorem. This quantitative bound controls the remainder in the harmonic-convolution formula for the squarefree reciprocal-totient sum. Together with the logarithmic-moment identity and the bound on its constant term, it supplies the large-cutoff estimate in the Ramaré argument. The exponent2/5 and endpoint16 are auxiliary choices of this formal development; the statement assumes no convergence or numerical estimate. Arithmetic functions vanish at zero, so the zero-index term contributes zero.
-- source:
--   O. Ramaré, On Shnirelman's constant, Ann. Scuola Norm. Sup. Pisa22 (1995),645–706, Section3, printed pp.656–660. https://www.numdam.org/item/ASNSP_1995_4_22_4_645_0/ . The weighted exponent2/5 is an auxiliary choice, not a verbatim source declaration. The exact correction construction is https://prove2.me/theorems/a866384b-78aa-46c7-90df-9bbecf5707a5 ; qualitative convergence is https://prove2.me/theorems/7395dd2e-3172-4af5-8d16-8debb89e26ed ; the harmonic-error consumer is https://prove2.me/theorems/c5e5cedf-d538-4888-b726-db041653e0b7 .

import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
set_option autoImplicit false
open scoped BigOperators

theorem RamareAnalytic.weighted_moment_le_sixteen
    (h : ArithmeticFunction ℝ) (hmul : h.IsMultiplicative)
    (hpv : ∀ p : ℕ, Nat.Prime p →
      h p = 1 / ((p : ℝ) * ((p : ℝ) - 1)) ∧
      h (p ^ 2) = -(1 / ((p : ℝ) * ((p : ℝ) - 1))))
    (hpz : ∀ p k : ℕ, Nat.Prime p → 3 ≤ k → h (p ^ k) = 0) :
    (∑' n : ℕ, |h n| * (n : ℝ) ^ (2 / 5 : ℝ)) ≤ 16 := by sorry
