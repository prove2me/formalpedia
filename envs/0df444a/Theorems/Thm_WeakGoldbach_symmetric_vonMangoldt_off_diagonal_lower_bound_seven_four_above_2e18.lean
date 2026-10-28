-- Prove2me | Theorems.Thm_WeakGoldbach_symmetric_vonMangoldt_off_diagonal_lower_bound_seven_four_above_2e18
-- name    : WeakGoldbach.symmetric_vonMangoldt_off_diagonal_lower_bound_seven_four_above_2e18
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T06:38:45.833322+00:00
-- url     : https://prove2.me/theorems/1cd0ac1d-972e-4876-a050-0e83d4d9ea27
-- title:
--   Off-diagonal $\tfrac74$ symmetric von Mangoldt lower bound above $2\cdot10^{18}$
-- statement:
--   For every natural number $m>2\cdot10^{18}$, write
--   $$
--   F(2m)=\prod_{\substack{p\mid 2m\\p>2}}\frac{p-1}{p-2},\qquad
--   O_m=\sum_{1\le t<m-1}\Lambda(m-t)\Lambda(m+t).
--   $$
--   The bound is
--   $$
--   O_m\ge\tfrac74 F(2m)m.
--   $$
--
--   Role: off-diagonal companion of `WeakGoldbach.symmetric_vonMangoldt_lower_bound_with_diagonal_seven_four_above_2e18`. Splitting the $t=0$ term gives $W_m=\Lambda(m)^2+O_m$, and the displayed estimate implies the with-diagonal $\tfrac74$ bound. Independent of the $\tfrac32$/triple/$7/4$-total ancestor chain.
--
--   This remains an open quantitative sufficient estimate.
-- source:
--   Reduction lemma for WeakGoldbach.symmetric_vonMangoldt_lower_bound_with_diagonal_seven_four_above_2e18. Parallel to off_diagonal nodes at 5/4 and 3/2. Avoids the 3/2 / triple / total-7/4 ancestor chain.

import Mathlib

namespace WeakGoldbach

theorem symmetric_vonMangoldt_off_diagonal_lower_bound_seven_four_above_2e18
    (m : Nat) (hm : 2 * 10 ^ 18 < m) :
    (7 / 4 : Real) *
        Finset.prod ((2 * m).primeFactors.filter (fun p => 2 < p))
          (fun p => ((p : Real) - 1) / ((p : Real) - 2)) *
        (m : Real)
      <= Finset.sum ((Finset.range (m - 1)).erase 0)
          (fun t => (ArithmeticFunction.vonMangoldt (m - t) : Real) *
            (ArithmeticFunction.vonMangoldt (m + t) : Real)) := by
  sorry

end WeakGoldbach
