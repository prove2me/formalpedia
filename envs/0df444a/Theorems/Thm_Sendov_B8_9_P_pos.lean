-- Prove2me | Theorems.Thm_Sendov_B8_9_P_pos
-- name    : Sendov.B8_9.P_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:06:18.808798+00:00
-- url     : https://prove2.me/theorems/f7251816-954d-5e7e-a18a-dbf910d5f81a
-- title:
--   B8 9: P pos
-- statement:
--   The certificate: `17 ^ 6 * P α` is a positive combination of `αʲ (17-α)^(6-j)`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree8_9.lean#L88-L113
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree8_9.lean#L88-L113

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree8_9
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B8_9
set_option maxHeartbeats 2000000

theorem Sendov.B8_9.P_pos {α : ℝ} (hα : 0 ≤ α) (hα' : α ≤ 4) :
    0 < 656208 + 407736 * α - 877827 * α ^ 2 + 621074 * α ^ 3 - 39267 * α ^ 4 - 5436 * α ^ 5 - 180 * α ^ 6 := by sorry
