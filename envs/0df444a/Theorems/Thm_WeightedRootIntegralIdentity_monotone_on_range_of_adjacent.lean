-- Prove2me | Theorems.Thm_WeightedRootIntegralIdentity_monotone_on_range_of_adjacent
-- name    : WeightedRootIntegralIdentity.monotone_on_range_of_adjacent
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-09-13T15:27:29.984849+00:00
-- url     : https://prove2.me/theorems/e9be3607-afc8-4185-8fde-bf7c857c957d
-- title:
--   Adjacent inequalities imply finite-range monotonicity
-- statement:
--   Let $a_0,\ldots,a_{n-1}$ be a finite real sequence satisfying $a_i\le a_{i+1}$ at every adjacent pair within its range. Then for every $i<j<n$,
--   $$
--   a_i\le a_j.
--   $$
--
--   This converts the adjacent monotonicity hypothesis used in the weighted integral identity into the global ordering needed to classify the signs of all factors on each interval.
-- source:
--   Elementary finite-order lemma supporting the ordered-node hypothesis in https://math.stackexchange.com/questions/4244874/can-we-prove-am-gm-inequality-using-these-integrals

import Mathlib

namespace WeightedRootIntegralIdentity

theorem monotone_on_range_of_adjacent
    (n : ℕ) (a : ℕ → ℝ)
    (hmono : ∀ i < n - 1, a i ≤ a (i + 1)) :
    ∀ i j, i < j → j < n → a i ≤ a j := by sorry

end WeightedRootIntegralIdentity
