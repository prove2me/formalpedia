-- Prove2me | Theorems.Thm_Sendov_B58_60_finite_range
-- name    : Sendov.B58_60.finite_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:46:46.944463+00:00
-- url     : https://prove2.me/theorems/4b9b9616-3ced-495f-a725-96a069ccd114
-- title:
--   B58 60: finite range
-- statement:
--   **The batch `58 ≤ n ≤ 60`.**
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree58_60.lean#L218-L245
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree58_60.lean#L218-L245

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree58_60
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B58_60
set_option maxHeartbeats 2000000

theorem Sendov.B58_60.finite_range {n : ℕ} (h0 : 58 ≤ n) (h1 : n ≤ 60) {α : ℝ}
    (hα : 0 ≤ α) (_hα' : α ≤ 17) (hfeas : c n α ^ 2 ≤ A n α) : R n α < 1 := by sorry
