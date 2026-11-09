-- Prove2me | Theorems.Thm_Pr6453_shifted_upper
-- name    : Pr6453.shifted_upper
-- status  : Proved
-- author  : @gustasmickus
-- created : 2026-11-08T17:43:41.04239+00:00
-- url     : https://prove2.me/theorems/968d9f41-5872-404d-9b5f-e3be9c0e35bf
-- title:
--   PR #6453: the remaining twenty shifted rank bounds
-- statement:
--   The other half of the rank bounds: the paid ranks $6$ to $56$ at exponent $1-t$, and all twelve paid ranks at exponent $1-t+\tfrac17$, each bounded above. The second group has $c = \tfrac17 - t \approx 0.1396$, so $|c\log r| \le 0.7$ and fourteen terms of the exponential series are used; the first group is the same as in the companion node with six terms.
-- source:
--   CrocSwap/integer-mult-bounds, PR #6453, head b1a3e525793eca35c56324aa7ffd0b714cf606d4, research/p104-third-anchor-clean-mixed-root/pricing.py (moments at 1-TESTED and 1-TESTED+1/7).

import Definitions.Def_Pr6453_RankMoments
import Definitions.Def_Pr6453_Strictification

set_option autoImplicit false

namespace Pr6453

theorem shifted_upper :
    (6:ℝ)^(1 - (tested:ℝ)) ≤ (5.964766572000 : ℝ) ∧
      (7:ℝ)^(1 - (tested:ℝ)) ≤ (6.955369182000 : ℝ) ∧
      (8:ℝ)^(1 - (tested:ℝ)) ≤ (7.945505142000 : ℝ) ∧
      (16:ℝ)^(1 - (tested:ℝ)) ≤ (15.854845612000 : ℝ) ∧
      (24:ℝ)^(1 - (tested:ℝ)) ≤ (23.750593201000 : ℝ) ∧
      (32:ℝ)^(1 - (tested:ℝ)) ≤ (31.637526487000 : ℝ) ∧
      (56:ℝ)^(1 - (tested:ℝ)) ≤ (55.263921597000 : ℝ) ∧
      (1:ℝ)^(1 - (tested:ℝ) + 1/7) ≤ (1.000000001000 : ℝ) ∧
      (2:ℝ)^(1 - (tested:ℝ) + 1/7) ≤ (2.203153666000 : ℝ) ∧
      (3:ℝ)^(1 - (tested:ℝ) + 1/7) ≤ (3.497140876000 : ℝ) ∧
      (4:ℝ)^(1 - (tested:ℝ) + 1/7) ≤ (4.853886076000 : ℝ) ∧
      (5:ℝ)^(1 - (tested:ℝ) + 1/7) ≤ (6.259293763000 : ℝ) ∧
      (6:ℝ)^(1 - (tested:ℝ) + 1/7) ≤ (7.704738741000 : ℝ) ∧
      (7:ℝ)^(1 - (tested:ℝ) + 1/7) ≤ (9.184351112000 : ℝ) ∧
      (8:ℝ)^(1 - (tested:ℝ) + 1/7) ≤ (10.693856903000 : ℝ) ∧
      (16:ℝ)^(1 - (tested:ℝ) + 1/7) ≤ (23.560210038000 : ℝ) ∧
      (24:ℝ)^(1 - (tested:ℝ) + 1/7) ≤ (37.397924090000 : ℝ) ∧
      (32:ℝ)^(1 - (tested:ℝ) + 1/7) ≤ (51.906763115000 : ℝ) ∧
      (56:ℝ)^(1 - (tested:ℝ) + 1/7) ≤ (98.216136531000 : ℝ) := by
  sorry

end Pr6453
