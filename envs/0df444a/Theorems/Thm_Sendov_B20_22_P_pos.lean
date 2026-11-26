-- Prove2me | Theorems.Thm_Sendov_B20_22_P_pos
-- name    : Sendov.B20_22.P_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:09:10.767421+00:00
-- url     : https://prove2.me/theorems/95c17b4e-ddd0-5cdc-b45b-7a5b36f59901
-- title:
--   B20 22: P pos
-- statement:
--   The certificate: `17 ^ 18 * P α` is a positive combination of `αʲ (17-α)^(18-j)`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree20_22.lean#L88-L137
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree20_22.lean#L88-L137

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree20_22
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B20_22
set_option maxHeartbeats 2000000

theorem Sendov.B20_22.P_pos {α : ℝ} (hα : 0 ≤ α) (hα' : α ≤ 21 / 2) :
    0 < 721140310389707127738 + 2170180610909239016088 * α + 2889750967198268814324 * α ^ 2 + 2227128338977232972904 * α ^ 3 + 1085997068794302710391 * α ^ 4 + 339049376116278228288 * α ^ 5 + 60509700204282383346 * α ^ 6 - 1038039442012938636 * α ^ 7 - 14060791839010189905 * α ^ 8 + 1774506642858471852 * α ^ 9 + 45855210342618468 * α ^ 10 + 226538249017920 * α ^ 11 - 222291771124416 * α ^ 12 - 18538380993792 * α ^ 13 - 787852835840 * α ^ 14 - 20286313472 * α ^ 15 - 320448768 * α ^ 16 - 2874368 * α ^ 17 - 11264 * α ^ 18 := by sorry
