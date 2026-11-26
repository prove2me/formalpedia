-- Prove2me | Theorems.Thm_Sendov_B64_69_finite_range
-- name    : Sendov.B64_69.finite_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:50:37.536011+00:00
-- url     : https://prove2.me/theorems/1a601a0a-dca2-421d-987d-124a537174a6
-- title:
--   B64 69: finite range
-- statement:
--   **The batch `64 ≤ n ≤ 69`.**
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree64_69.lean#L230-L257
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree64_69.lean#L230-L257

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree64_69
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B64_69
set_option maxHeartbeats 2000000

theorem Sendov.B64_69.finite_range {n : ℕ} (h0 : 64 ≤ n) (h1 : n ≤ 69) {α : ℝ}
    (hα : 0 ≤ α) (_hα' : α ≤ 17) (hfeas : c n α ^ 2 ≤ A n α) : R n α < 1 := by sorry
