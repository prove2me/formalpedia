-- Prove2me | Theorems.Thm_WeakGoldbach_symmetric_vonMangoldt_lower_bound_with_diagonal_triple_above_2e18
-- name    : WeakGoldbach.symmetric_vonMangoldt_lower_bound_with_diagonal_triple_above_2e18
-- status  : Open
-- author  : @Ethan
-- created : 2026-10-21T05:31:26.791374+00:00
-- url     : https://prove2.me/theorems/4334ca3a-9b23-4154-a810-5d3dfc315fde
-- title:
--   Diagonal-corrected $\tfrac32$ symmetric von Mangoldt lower bound above $2\cdot10^{18}$
-- statement:
--   For every natural number $m>2\cdot10^{18}$, let
--   $$
--   F(2m)=\prod_{\substack{p\mid 2m\\p>2}}\frac{p-1}{p-2},\qquad
--   W_m=\sum_{t=0}^{m-2}\Lambda(m-t)\Lambda(m+t),
--   $$
--   where $\Lambda$ is the von Mangoldt function. The bound is
--   $$
--   W_m\ge \frac32 F(2m)m+\frac12\Lambda(m)^2.
--   $$
--
--   Role: this is the diagonal-corrected symmetric-sum estimate needed to deduce `WeakGoldbach.integral_main_term_triple_above_2e18` from the identity $R(2m)=2W_m-\Lambda(m)^2$. Doubling the displayed inequality and subtracting the diagonal term yields $\operatorname{Re} R(2m)\ge 3\,F(2m)\,m$. It is the exact analogue of `WeakGoldbach.symmetric_vonMangoldt_lower_bound_with_diagonal_above_2e18`, with coefficient $\tfrac32$ in place of $\tfrac54$ (matching the integral constants $3$ and $\tfrac52$ respectively).
--
--   This remains an open quantitative sufficient estimate at the finite threshold $m>2\cdot10^{18}$.
-- source:
--   Reduction lemma for WeakGoldbach.integral_main_term_triple_above_2e18. Parallel to WeakGoldbach.symmetric_vonMangoldt_lower_bound_with_diagonal_above_2e18 (coefficient 3/2 in place of 5/4). The identity R(2m)=2W_m−Λ(m)^2 is recorded in WeakGoldbach.binary_count_symmetric; normalization as in Pintz arXiv:1804.09084 §2 (2.9).

import Mathlib

namespace WeakGoldbach

theorem symmetric_vonMangoldt_lower_bound_with_diagonal_triple_above_2e18
    (m : ℕ) (hm : 2 * 10 ^ 18 < m) :
    (3 / 2 : ℝ) *
        (∏ p ∈ (2 * m).primeFactors.filter (2 < ·), ((p : ℝ) - 1) / ((p : ℝ) - 2)) *
        (m : ℝ)
      + ((ArithmeticFunction.vonMangoldt m : ℝ) ^ 2) / 2
      ≤ ∑ t ∈ Finset.range (m - 1),
          (ArithmeticFunction.vonMangoldt (m - t) : ℝ) *
            (ArithmeticFunction.vonMangoldt (m + t) : ℝ) := by
  sorry

end WeakGoldbach
