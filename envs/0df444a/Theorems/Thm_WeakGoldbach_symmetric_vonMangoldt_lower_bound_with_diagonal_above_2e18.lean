-- Prove2me | Theorems.Thm_WeakGoldbach_symmetric_vonMangoldt_lower_bound_with_diagonal_above_2e18
-- name    : WeakGoldbach.symmetric_vonMangoldt_lower_bound_with_diagonal_above_2e18
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-09-25T13:51:29.174632+00:00
-- url     : https://prove2.me/theorems/44436c12-a5b0-4a0e-899d-ec908c4a4694
-- title:
--   Symmetric von Mangoldt lower bound with diagonal correction above $2\cdot10^{18}$
-- statement:
--   For every natural number $m>2\cdot10^{18}$, let
--   $$F(2m)=\prod_{\substack{p\mid 2m\\p>2}}\frac{p-1}{p-2},\qquad
--   W_m=\sum_{t=0}^{m-2}\Lambda(m-t)\Lambda(m+t),$$
--   where $\Lambda$ is the von Mangoldt function. The bound is
--   $$W_m\ge \frac54 F(2m)m+\frac12\Lambda(m)^2.$$
-- source:
--   Reduction lemma for WeakGoldbach.integral_main_term_above_2e18. The source target records the identity R(2m)=2W_m−Λ(m)^2 and requires the diagonal term to be absorbed; this child isolates the corrected symmetric von Mangoldt estimate.

import Mathlib

namespace WeakGoldbach

theorem symmetric_vonMangoldt_lower_bound_with_diagonal_above_2e18
    (m : ℕ) (hm : 2 * 10 ^ 18 < m) :
    (5 / 4 : ℝ) *
        (∏ p ∈ (2 * m).primeFactors.filter (2 < ·), ((p : ℝ) - 1) / ((p : ℝ) - 2)) *
        (m : ℝ)
      + ((ArithmeticFunction.vonMangoldt m : ℝ) ^ 2) / 2
      ≤ ∑ t ∈ Finset.range (m - 1),
          (ArithmeticFunction.vonMangoldt (m - t) : ℝ) *
            (ArithmeticFunction.vonMangoldt (m + t) : ℝ) := by
  sorry

end WeakGoldbach
