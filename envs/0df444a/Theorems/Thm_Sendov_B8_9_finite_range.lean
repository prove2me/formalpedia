-- Prove2me | Theorems.Thm_Sendov_B8_9_finite_range
-- name    : Sendov.B8_9.finite_range
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T18:21:36.806854+00:00
-- url     : https://prove2.me/theorems/61702fec-f6d7-5988-ae11-3fb862b7a9b2
-- title:
--   B8 9: finite range
-- statement:
--   **The batch `8 ≤ n ≤ 9`.**
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree8_9.lean#L118-L145
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree8_9.lean#L118-L145

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree8_9
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B8_9
set_option maxHeartbeats 2000000

theorem Sendov.B8_9.finite_range {n : ℕ} (h0 : 8 ≤ n) (h1 : n ≤ 9) {α : ℝ}
    (hα : 0 ≤ α) (_hα' : α ≤ 17) (hfeas : c n α ^ 2 ≤ A n α) : R n α < 1 := by sorry
