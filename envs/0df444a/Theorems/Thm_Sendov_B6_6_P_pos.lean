-- Prove2me | Theorems.Thm_Sendov_B6_6_P_pos
-- name    : Sendov.B6_6.P_pos
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T18:06:08.778866+00:00
-- url     : https://prove2.me/theorems/861fa48b-5703-46bf-97d2-5cb2a8a34d2a
-- title:
--   B6 6: P pos
-- statement:
--   The certificate: `17 ^ 4 * P α` is a positive combination of `αʲ (17-α)^(4-j)`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree6_6.lean#L88-L109
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree6_6.lean#L88-L109

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree6_6
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B6_6
set_option maxHeartbeats 2000000

theorem Sendov.B6_6.P_pos {α : ℝ} (hα : 0 ≤ α) (hα' : α ≤ 5 / 2) :
    0 < 1575 - 900 * α + 2345 * α ^ 2 - 342 * α ^ 3 - 24 * α ^ 4 := by sorry
