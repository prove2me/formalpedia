-- Prove2me | Theorems.Thm_Sendov_B14_15_finite_range
-- name    : Sendov.B14_15.finite_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:24:26.534394+00:00
-- url     : https://prove2.me/theorems/1521f8a2-7be5-5202-a60b-be64488a4b35
-- title:
--   B14 15: finite range
-- statement:
--   **The batch `14 ≤ n ≤ 15`.**
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree14_15.lean#L130-L157
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree14_15.lean#L130-L157

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree14_15
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B14_15
set_option maxHeartbeats 2000000

theorem Sendov.B14_15.finite_range {n : ℕ} (h0 : 14 ≤ n) (h1 : n ≤ 15) {α : ℝ}
    (hα : 0 ≤ α) (_hα' : α ≤ 17) (hfeas : c n α ^ 2 ≤ A n α) : R n α < 1 := by sorry
