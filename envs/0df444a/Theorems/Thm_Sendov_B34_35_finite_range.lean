-- Prove2me | Theorems.Thm_Sendov_B34_35_finite_range
-- name    : Sendov.B34_35.finite_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:33:42.801815+00:00
-- url     : https://prove2.me/theorems/2b00b8b7-aa67-4b49-af50-cb24dad14459
-- title:
--   B34 35: finite range
-- statement:
--   **The batch `34 ≤ n ≤ 35`.**
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree34_35.lean#L170-L197
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree34_35.lean#L170-L197

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree34_35
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B34_35
set_option maxHeartbeats 2000000

theorem Sendov.B34_35.finite_range {n : ℕ} (h0 : 34 ≤ n) (h1 : n ≤ 35) {α : ℝ}
    (hα : 0 ≤ α) (_hα' : α ≤ 17) (hfeas : c n α ^ 2 ≤ A n α) : R n α < 1 := by sorry
