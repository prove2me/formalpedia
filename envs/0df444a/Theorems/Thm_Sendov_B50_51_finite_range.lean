-- Prove2me | Theorems.Thm_Sendov_B50_51_finite_range
-- name    : Sendov.B50_51.finite_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:40:52.624558+00:00
-- url     : https://prove2.me/theorems/e409e974-8150-4914-b3f5-4a739580768a
-- title:
--   B50 51: finite range
-- statement:
--   **The batch `50 ≤ n ≤ 51`.**
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree50_51.lean#L202-L229
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree50_51.lean#L202-L229

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree50_51
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B50_51
set_option maxHeartbeats 2000000

theorem Sendov.B50_51.finite_range {n : ℕ} (h0 : 50 ≤ n) (h1 : n ≤ 51) {α : ℝ}
    (hα : 0 ≤ α) (_hα' : α ≤ 17) (hfeas : c n α ^ 2 ≤ A n α) : R n α < 1 := by sorry
