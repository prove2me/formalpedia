-- Prove2me | Theorems.Thm_WeakGoldbach_symmetric_vonMangoldt_total_with_7_4_margin_above_2e18
-- name    : WeakGoldbach.symmetric_vonMangoldt_total_with_7_4_margin_above_2e18
-- status  : Open
-- author  : @Ethan
-- created : 2026-10-21T05:39:55.460559+00:00
-- url     : https://prove2.me/theorems/b13acb86-cee8-4443-b13d-85f4735bd848
-- title:
--   A $7/4$ margin for the full symmetric von Mangoldt sum above $2\cdot10^{18}$
-- statement:
--   For every natural number $m>2\cdot10^{18}$, the full symmetric von Mangoldt sum satisfies
--
--   $$
--   W_m=\sum_{0\le t<m-1}\Lambda(m-t)\Lambda(m+t)
--   \;\ge\;
--   \tfrac74\,F(2m)\,m,
--   \qquad
--   F(2m)=\prod_{\substack{p\mid 2m\\p>2}}\frac{p-1}{p-2}.
--   $$
--
--   Role: this is the full-sum companion of `WeakGoldbach.symmetric_vonMangoldt_off_diagonal_lower_bound_triple_above_2e18`. Combined with the proved diagonal bound $\Lambda(m)^2\le\tfrac14 F(2m)m$, it yields the off-diagonal estimate
--   $$
--   W_m-\Lambda(m)^2\ge\bigl(\tfrac74-\tfrac14\bigr)F(2m)m=\tfrac32 F(2m)m.
--   $$
--   The coefficient $\tfrac74$ is exactly $\tfrac32+\tfrac14$, so the diagonal absorption introduces no extra slack beyond the known $\tfrac14$ diagonal majorant. The construction is parallel to the reduction of the $\tfrac54$ off-diagonal node from the $\tfrac32$ full-sum margin, but uses a fresh full-sum leaf so as not to depend on that $\tfrac32$ margin or its integral/diagonal descendants.
--
--   This remains an open quantitative sufficient estimate at the stated finite threshold.
-- source:
--   Full-sum companion for WeakGoldbach.symmetric_vonMangoldt_off_diagonal_lower_bound_triple_above_2e18. Diagonal absorption uses WeakGoldbach.vonMangoldt_diagonal_small_above_2e18 (proved, coefficient 1/4). Parallel to the pair (total 3/2 margin, off-diagonal 5/4); here the pair is (total 7/4, off-diagonal 3/2). Hardy–Littlewood singular-series heuristics motivate the shape; no source asserts this finite-threshold inequality.

import Mathlib

namespace WeakGoldbach

theorem symmetric_vonMangoldt_total_with_7_4_margin_above_2e18 (m : Nat) (hm : 2 * 10 ^ 18 < m) :
    (7 / 4 : Real) * Finset.prod ((2 * m).primeFactors.filter (fun p => 2 < p))
        (fun p => ((p : Real) - 1) / ((p : Real) - 2)) * (m : Real) <=
      Finset.sum (Finset.range (m - 1))
        (fun t => (ArithmeticFunction.vonMangoldt (m - t) : Real) *
          (ArithmeticFunction.vonMangoldt (m + t) : Real)) := by
  sorry

end WeakGoldbach
