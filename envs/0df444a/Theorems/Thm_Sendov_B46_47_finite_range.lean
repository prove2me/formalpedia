-- Prove2me | Theorems.Thm_Sendov_B46_47_finite_range
-- name    : Sendov.B46_47.finite_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:39:16.222356+00:00
-- url     : https://prove2.me/theorems/c882bd66-488b-4f6b-9795-1f970dd4744a
-- title:
--   B46 47: finite range
-- statement:
--   **The batch `46 ≤ n ≤ 47`.**
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree46_47.lean#L194-L221
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree46_47.lean#L194-L221

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree46_47
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B46_47
set_option maxHeartbeats 2000000

theorem Sendov.B46_47.finite_range {n : ℕ} (h0 : 46 ≤ n) (h1 : n ≤ 47) {α : ℝ}
    (hα : 0 ≤ α) (_hα' : α ≤ 17) (hfeas : c n α ^ 2 ≤ A n α) : R n α < 1 := by sorry
