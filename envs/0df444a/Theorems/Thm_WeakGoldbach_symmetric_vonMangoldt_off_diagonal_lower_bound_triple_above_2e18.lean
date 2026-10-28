-- Prove2me | Theorems.Thm_WeakGoldbach_symmetric_vonMangoldt_off_diagonal_lower_bound_triple_above_2e18
-- name    : WeakGoldbach.symmetric_vonMangoldt_off_diagonal_lower_bound_triple_above_2e18
-- status  : Open
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T05:34:52.926883+00:00
-- url     : https://prove2.me/theorems/cbaa1a76-3617-4d0d-827f-b80504ad99bd
-- title:
--   Off-diagonal $\tfrac32$ symmetric von Mangoldt lower bound above $2\cdot10^{18}$
-- statement:
--   For every natural number $m$ greater than $2\cdot10^{18}$, the sum of the symmetric von Mangoldt products over offsets $1\le t<m-1$ is at least $\tfrac32$ times $m$ times the singular-series factor over odd prime divisors of $2m$:
--
--   $$
--   \sum_{1\le t<m-1}\Lambda(m-t)\Lambda(m+t)
--   \;\ge\;
--   \tfrac32\,F(2m)\,m,
--   \qquad
--   F(2m)=\prod_{\substack{p\mid 2m\\p>2}}\frac{p-1}{p-2}.
--   $$
--
--   Role: this isolates the off-diagonal contribution needed for `WeakGoldbach.symmetric_vonMangoldt_lower_bound_with_diagonal_triple_above_2e18`. Writing $W_m$ for the full sum (including $t=0$) one has $W_m=\Lambda(m)^2+\sum_{t\ne0}$, so an off-diagonal lower bound of $\tfrac32 F(2m)m$ upgrades immediately to
--   $$
--   W_m\ge\tfrac32 F(2m)m+\Lambda(m)^2\ge\tfrac32 F(2m)m+\tfrac12\Lambda(m)^2.
--   $$
--   It is the exact analogue of `WeakGoldbach.symmetric_vonMangoldt_off_diagonal_lower_bound_above_2e18` with coefficient $\tfrac32$ in place of $\tfrac54$.
--
--   This is an open quantitative sufficient estimate at the stated finite threshold; it is not derived here from the full-sum $\tfrac32$ margin or from the circle-method integral form, so that those nodes remain independent of this leaf.
-- source:
--   Off-diagonal strengthening for WeakGoldbach.symmetric_vonMangoldt_lower_bound_with_diagonal_triple_above_2e18. Parallel to WeakGoldbach.symmetric_vonMangoldt_off_diagonal_lower_bound_above_2e18 (coefficient 3/2 in place of 5/4). Hardy–Littlewood singular-series main term motivates the shape; the cited conjectural literature does not assert or prove this finite-threshold inequality.

import Mathlib

namespace WeakGoldbach

theorem symmetric_vonMangoldt_off_diagonal_lower_bound_triple_above_2e18
    (m : Nat) (hm : 2 * 10 ^ 18 < m) :
    (3 / 2 : Real) *
        Finset.prod ((2 * m).primeFactors.filter (fun p => 2 < p))
          (fun p => ((p : Real) - 1) / ((p : Real) - 2)) *
        (m : Real)
      <= Finset.sum ((Finset.range (m - 1)).erase 0)
          (fun t => (ArithmeticFunction.vonMangoldt (m - t) : Real) *
            (ArithmeticFunction.vonMangoldt (m + t) : Real)) := by
  sorry

end WeakGoldbach
