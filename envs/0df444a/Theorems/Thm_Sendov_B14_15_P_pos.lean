-- Prove2me | Theorems.Thm_Sendov_B14_15_P_pos
-- name    : Sendov.B14_15.P_pos
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T18:07:29.603797+00:00
-- url     : https://prove2.me/theorems/78e03de1-b046-4211-9026-fb47069d4994
-- title:
--   B14 15: P pos
-- statement:
--   The certificate: `17 ^ 12 * P α` is a positive combination of `αʲ (17-α)^(12-j)`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree14_15.lean#L88-L125
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree14_15.lean#L88-L125

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree14_15
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B14_15
set_option maxHeartbeats 2000000

theorem Sendov.B14_15.P_pos {α : ℝ} (hα : 0 ≤ α) (hα' : α ≤ 7) :
    0 < 4540012290450 + 9000770719122 * α + 7217967952260 * α ^ 2 + 2789503991820 * α ^ 3 + 226924812075 * α ^ 4 - 867448623285 * α ^ 5 + 235182487819 * α ^ 6 + 1315276135 * α ^ 7 - 765536900 * α ^ 8 - 78585080 * α ^ 9 - 3463520 * α ^ 10 - 74480 * α ^ 11 - 640 * α ^ 12 := by sorry
