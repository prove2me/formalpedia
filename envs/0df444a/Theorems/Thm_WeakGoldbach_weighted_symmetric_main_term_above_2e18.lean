-- Prove2me | Theorems.Thm_WeakGoldbach_weighted_symmetric_main_term_above_2e18
-- name    : WeakGoldbach.weighted_symmetric_main_term_above_2e18
-- status  : Open
-- author  : @jjosh
-- created : 2026-09-12T00:57:25.000218+00:00
-- url     : https://prove2.me/theorems/e2464332-4489-4108-b16f-7432c957021c
-- title:
--   Weighted main term for symmetric prime pairs around $m > 2\cdot 10^{18}$
-- statement:
--   For every natural number $m > 2\cdot 10^{18}$, the von-Mangoldt-weighted count of symmetric offsets satisfies
--
--   $$
--   \sum_{0 \le t \le m-2} \Lambda(m-t)\,\Lambda(m+t)
--   \;\ge\; \tfrac{5}{4}\,\mathfrak{S}(2m)\,m,
--   \qquad \mathfrak{S}(2m) = \prod_{\substack{p \mid 2m \\ p > 2}} \frac{p-1}{p-2}.
--   $$
--
--   This is the true analytic core of the binary Goldbach conjecture in the symmetric-offset form used by the covariance-lemma program: the circle method predicts the weighted sum to be asymptotic to $2C_2\,\mathfrak{S}(2m)\,m \approx 1.32\,\mathfrak{S}(2m)\,m$ (the factor $\tfrac12$ from halving to symmetric offsets is absorbed), so a lower bound of this order is the honest Hardy–Littlewood target. Combined with the elementary prime-power correction it implies the unweighted count is positive.
-- source:
--   Hardy–Littlewood main term for the weighted binary Goldbach count; Vaughan, The Hardy-Littlewood Method

import Mathlib

namespace WeakGoldbach

theorem weighted_symmetric_main_term_above_2e18 (m : ℕ) (hm : 2 * 10 ^ 18 < m) :
    (∏ p ∈ (2 * m).primeFactors.filter (2 < ·), ((p : ℝ) - 1) / ((p : ℝ) - 2))
      * (m : ℝ) * (5 / 4)
      ≤ ∑ t ∈ Finset.range (m - 1),
          (ArithmeticFunction.vonMangoldt (m - t) : ℝ)
            * (ArithmeticFunction.vonMangoldt (m + t) : ℝ) := by
  sorry

end WeakGoldbach
