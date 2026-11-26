-- Prove2me | Theorems.Thm_Sendov_B10_11_P_pos
-- name    : Sendov.B10_11.P_pos
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T18:06:33.653225+00:00
-- url     : https://prove2.me/theorems/317e40fa-589c-5920-b3e9-a9b328b87a19
-- title:
--   B10 11: P pos
-- statement:
--   The certificate: `17 ^ 8 * P α` is a positive combination of `αʲ (17-α)^(8-j)`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree10_11.lean#L88-L117
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree10_11.lean#L88-L117

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree10_11
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B10_11
set_option maxHeartbeats 2000000

theorem Sendov.B10_11.P_pos {α : ℝ} (hα : 0 ≤ α) (hα' : α ≤ 5) :
    0 < 32349375 + 39180105 * α + 10086687 * α ^ 2 - 24445935 * α ^ 3 + 11871036 * α ^ 4 - 351846 * α ^ 5 - 81598 * α ^ 6 - 4664 * α ^ 7 - 88 * α ^ 8 := by sorry
