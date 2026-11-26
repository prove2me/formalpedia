-- Prove2me | Theorems.Thm_Sendov_B38_39_finite_range
-- name    : Sendov.B38_39.finite_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:35:43.957274+00:00
-- url     : https://prove2.me/theorems/78dddb50-b157-4979-b941-e7083973e4eb
-- title:
--   B38 39: finite range
-- statement:
--   **The batch `38 ≤ n ≤ 39`.**
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree38_39.lean#L178-L205
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree38_39.lean#L178-L205

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree38_39
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B38_39
set_option maxHeartbeats 2000000

theorem Sendov.B38_39.finite_range {n : ℕ} (h0 : 38 ≤ n) (h1 : n ≤ 39) {α : ℝ}
    (hα : 0 ≤ α) (_hα' : α ≤ 17) (hfeas : c n α ^ 2 ≤ A n α) : R n α < 1 := by sorry
