-- Prove2me | Theorems.Thm_Sendov_B16_18_P_pos
-- name    : Sendov.B16_18.P_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:07:38.32719+00:00
-- url     : https://prove2.me/theorems/a447f789-af75-5d22-afe5-f696cae457d1
-- title:
--   B16 18: P pos
-- statement:
--   The certificate: `17 ^ 14 * P α` is a positive combination of `αʲ (17-α)^(14-j)`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree16_18.lean#L88-L129
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree16_18.lean#L88-L129

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree16_18
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B16_18
set_option maxHeartbeats 2000000

theorem Sendov.B16_18.P_pos {α : ℝ} (hα : 0 ≤ α) (hα' : α ≤ 17 / 2) :
    0 < 308547940078125 + 716274580556250 * α + 701075142421875 * α ^ 2 + 366034929547500 * α ^ 3 + 98713082723625 * α ^ 4 - 785317395690 * α ^ 5 - 34202916258669 * α ^ 6 + 6366700041480 * α ^ 7 + 121732471512 * α ^ 8 - 9494954208 * α ^ 9 - 1551607200 * α ^ 10 - 87661568 * α ^ 11 - 2586240 * α ^ 12 - 39936 * α ^ 13 - 256 * α ^ 14 := by sorry
