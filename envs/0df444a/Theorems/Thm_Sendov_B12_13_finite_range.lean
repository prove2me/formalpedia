-- Prove2me | Theorems.Thm_Sendov_B12_13_finite_range
-- name    : Sendov.B12_13.finite_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:23:15.763576+00:00
-- url     : https://prove2.me/theorems/a84c31ca-f816-4719-ab18-32d9373604ee
-- title:
--   B12 13: finite range
-- statement:
--   **The batch `12 ≤ n ≤ 13`.**
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree12_13.lean#L126-L153
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree12_13.lean#L126-L153

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree12_13
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B12_13
set_option maxHeartbeats 2000000

theorem Sendov.B12_13.finite_range {n : ℕ} (h0 : 12 ≤ n) (h1 : n ≤ 13) {α : ℝ}
    (hα : 0 ≤ α) (_hα' : α ≤ 17) (hfeas : c n α ^ 2 ≤ A n α) : R n α < 1 := by sorry
