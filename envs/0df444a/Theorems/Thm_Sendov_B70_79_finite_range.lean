-- Prove2me | Theorems.Thm_Sendov_B70_79_finite_range
-- name    : Sendov.B70_79.finite_range
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T18:51:16.73542+00:00
-- url     : https://prove2.me/theorems/164f6bd9-9aba-5171-8100-d0462f8d1d72
-- title:
--   B70 79: finite range
-- statement:
--   **The batch `70 ≤ n ≤ 79`.**
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree70_79.lean#L242-L269
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree70_79.lean#L242-L269

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree70_79
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B70_79
set_option maxHeartbeats 2000000

theorem Sendov.B70_79.finite_range {n : ℕ} (h0 : 70 ≤ n) (h1 : n ≤ 79) {α : ℝ}
    (hα : 0 ≤ α) (_hα' : α ≤ 17) (hfeas : c n α ^ 2 ≤ A n α) : R n α < 1 := by sorry
