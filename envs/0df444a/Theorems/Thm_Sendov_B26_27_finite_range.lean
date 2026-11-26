-- Prove2me | Theorems.Thm_Sendov_B26_27_finite_range
-- name    : Sendov.B26_27.finite_range
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T18:29:28.570628+00:00
-- url     : https://prove2.me/theorems/41d7c66f-daf9-5a6d-89ee-4a160965c0e9
-- title:
--   B26 27: finite range
-- statement:
--   **The batch `26 ≤ n ≤ 27`.**
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree26_27.lean#L154-L181
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree26_27.lean#L154-L181

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree26_27
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B26_27
set_option maxHeartbeats 2000000

theorem Sendov.B26_27.finite_range {n : ℕ} (h0 : 26 ≤ n) (h1 : n ≤ 27) {α : ℝ}
    (hα : 0 ≤ α) (_hα' : α ≤ 17) (hfeas : c n α ^ 2 ≤ A n α) : R n α < 1 := by sorry
