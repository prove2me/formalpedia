-- Prove2me | Theorems.Thm_Sendov_B12_13_P_pos
-- name    : Sendov.B12_13.P_pos
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T18:06:57.321066+00:00
-- url     : https://prove2.me/theorems/6b2b8551-0f61-5d8e-a648-187b421047e0
-- title:
--   B12 13: P pos
-- statement:
--   The certificate: `17 ^ 10 * P α` is a positive combination of `αʲ (17-α)^(10-j)`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree12_13.lean#L88-L121
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree12_13.lean#L88-L121

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree12_13
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B12_13
set_option maxHeartbeats 2000000

theorem Sendov.B12_13.P_pos {α : ℝ} (hα : 0 ≤ α) (hα' : α ≤ 6) :
    0 < 67214552328 + 108758874312 * α + 64248083658 * α ^ 2 + 8893434528 * α ^ 3 - 26471207052 * α ^ 4 + 9402730740 * α ^ 5 - 77587159 * α ^ 6 - 46242248 * α ^ 7 - 3634800 * α ^ 8 - 118976 * α ^ 9 - 1456 * α ^ 10 := by sorry
