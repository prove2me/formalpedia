-- Prove2me | Theorems.Thm_Sendov_B30_31_finite_range
-- name    : Sendov.B30_31.finite_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:31:24.47695+00:00
-- url     : https://prove2.me/theorems/b5cf8a2a-aa9b-4f01-ba15-b395027c6221
-- title:
--   B30 31: finite range
-- statement:
--   **The batch `30 ≤ n ≤ 31`.**
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree30_31.lean#L162-L189
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree30_31.lean#L162-L189

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree30_31
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B30_31
set_option maxHeartbeats 2000000

theorem Sendov.B30_31.finite_range {n : ℕ} (h0 : 30 ≤ n) (h1 : n ≤ 31) {α : ℝ}
    (hα : 0 ≤ α) (_hα' : α ≤ 17) (hfeas : c n α ^ 2 ≤ A n α) : R n α < 1 := by sorry
