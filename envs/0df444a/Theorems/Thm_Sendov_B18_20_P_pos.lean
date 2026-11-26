-- Prove2me | Theorems.Thm_Sendov_B18_20_P_pos
-- name    : Sendov.B18_20.P_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:07:56.41873+00:00
-- url     : https://prove2.me/theorems/ea27392e-1c22-5514-b990-5ccd58c13c8a
-- title:
--   B18 20: P pos
-- statement:
--   The certificate: `17 ^ 16 * P α` is a positive combination of `αʲ (17-α)^(16-j)`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree18_20.lean#L88-L133
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree18_20.lean#L88-L133

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree18_20
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B18_20
set_option maxHeartbeats 2000000

theorem Sendov.B18_20.P_pos {α : ℝ} (hα : 0 ≤ α) (hα' : α ≤ 19 / 2) :
    0 < 1996938880799635773 + 5327542416376042533 * α + 6168567333266685756 * α ^ 2 + 4015726419901684032 * α ^ 3 + 1568562341575363317 * α ^ 4 + 336439630979056719 * α ^ 5 - 5059047712773960 * α ^ 6 - 94154641040290584 * α ^ 7 + 14305270642714822 * α ^ 8 + 337895936432856 * α ^ 9 - 7990669279488 * α ^ 10 - 2592154628256 * α ^ 11 - 177335477376 * α ^ 12 - 6421337472 * α ^ 13 - 134803968 * α ^ 14 - 1555968 * α ^ 15 - 7680 * α ^ 16 := by sorry
