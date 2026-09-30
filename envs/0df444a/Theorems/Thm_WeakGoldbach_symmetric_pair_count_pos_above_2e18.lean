-- Prove2me | Theorems.Thm_WeakGoldbach_symmetric_pair_count_pos_above_2e18
-- name    : WeakGoldbach.symmetric_pair_count_pos_above_2e18
-- status  : Open
-- author  : @jjosh
-- created : 2026-09-11T22:44:05.110048+00:00
-- url     : https://prove2.me/theorems/57049e76-9b8c-4ccb-bb45-04026d0aae36
-- title:
--   Positive count of symmetric prime offsets around $m > 2\cdot 10^{18}$
-- statement:
--   For every natural number $m > 2\cdot 10^{18}$, the counting function
--
--   $$
--   R(m) = \#\{t \le m - 2 : \text{both } m - t \text{ and } m + t \text{ are prime}\}
--   $$
--
--   is positive. Since $2m = (m-t) + (m+t)$, this is the counting-function form of the even Goldbach conjecture — the quantity the circle method estimates, and the positivity claim that every attempted proof must establish.
-- source:
--   Counting-function form of the Goldbach conjecture

import Mathlib

namespace WeakGoldbach

theorem symmetric_pair_count_pos_above_2e18 (m : ℕ) (hm : 2 * 10 ^ 18 < m) :
    0 < ((Finset.range (m - 1)).filter
      (fun t => Nat.Prime (m - t) ∧ Nat.Prime (m + t))).card := by
  sorry

end WeakGoldbach
