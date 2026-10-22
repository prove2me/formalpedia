-- Prove2me | Theorems.Thm_WeakGoldbach_symmetric_vonMangoldt_lower_bound_with_diagonal_seven_four_above_2e18
-- name    : WeakGoldbach.symmetric_vonMangoldt_lower_bound_with_diagonal_seven_four_above_2e18
-- status  : Open
-- author  : @Ethan Cheung
-- created : 2026-10-21T06:31:06.707981+00:00
-- url     : https://prove2.me/theorems/22645f86-2177-490e-a9f8-0bea330e94ac
-- title:
--   Diagonal-corrected $\tfrac74$ symmetric von Mangoldt lower bound above $2\cdot10^{18}$
-- statement:
--   For every natural number $m>2\cdot10^{18}$, let
--   $$
--   F(2m)=\prod_{\substack{p\mid 2m\\p>2}}\frac{p-1}{p-2},\qquad
--   W_m=\sum_{t=0}^{m-2}\Lambda(m-t)\Lambda(m+t).
--   $$
--   The bound is
--   $$
--   W_m\ge \tfrac74 F(2m)m+\tfrac12\Lambda(m)^2.
--   $$
--
--   Role: diagonal-corrected companion of `WeakGoldbach.integral_main_term_seven_halves_above_2e18`. Doubling and subtracting the diagonal in $R(2m)=2W_m-\Lambda(m)^2$ yields $\operatorname{Re} R(2m)\ge\tfrac72 F(2m)m$. Analogue of the $\tfrac54$ and $\tfrac32$ with-diagonal nodes; independent of those ancestors.
--
--   This remains an open quantitative sufficient estimate.
-- source:
--   Reduction lemma for WeakGoldbach.integral_main_term_seven_halves_above_2e18. Parallel to with_diagonal nodes at 5/4 and 3/2. Identity R(2m)=2W_m−Λ(m)^2 from binary_count_symmetric.

import Mathlib

namespace WeakGoldbach

theorem symmetric_vonMangoldt_lower_bound_with_diagonal_seven_four_above_2e18
    (m : ℕ) (hm : 2 * 10 ^ 18 < m) :
    (7 / 4 : ℝ) *
        (∏ p ∈ (2 * m).primeFactors.filter (2 < ·), ((p : ℝ) - 1) / ((p : ℝ) - 2)) *
        (m : ℝ)
      + ((ArithmeticFunction.vonMangoldt m : ℝ) ^ 2) / 2
      ≤ ∑ t ∈ Finset.range (m - 1),
          (ArithmeticFunction.vonMangoldt (m - t) : ℝ) *
            (ArithmeticFunction.vonMangoldt (m + t) : ℝ) := by
  sorry

end WeakGoldbach
