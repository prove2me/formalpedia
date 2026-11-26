-- Prove2me | Theorems.Thm_Sendov_B10_11_finite_range
-- name    : Sendov.B10_11.finite_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:22:17.550816+00:00
-- url     : https://prove2.me/theorems/36f9d03b-c84d-5dfb-bdb3-b79b1341244e
-- title:
--   B10 11: finite range
-- statement:
--   **The batch `10 ≤ n ≤ 11`.**
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree10_11.lean#L122-L149
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree10_11.lean#L122-L149

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree10_11
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B10_11
set_option maxHeartbeats 2000000

theorem Sendov.B10_11.finite_range {n : ℕ} (h0 : 10 ≤ n) (h1 : n ≤ 11) {α : ℝ}
    (hα : 0 ≤ α) (_hα' : α ≤ 17) (hfeas : c n α ^ 2 ≤ A n α) : R n α < 1 := by sorry
