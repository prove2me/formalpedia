-- Prove2me | Theorems.Thm_Sendov_B32_33_finite_range
-- name    : Sendov.B32_33.finite_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:33:04.787323+00:00
-- url     : https://prove2.me/theorems/fe45292d-2513-446e-a82f-5837dec7e5c7
-- title:
--   B32 33: finite range
-- statement:
--   **The batch `32 ≤ n ≤ 33`.**
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree32_33.lean#L166-L193
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree32_33.lean#L166-L193

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree32_33
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B32_33
set_option maxHeartbeats 2000000

theorem Sendov.B32_33.finite_range {n : ℕ} (h0 : 32 ≤ n) (h1 : n ≤ 33) {α : ℝ}
    (hα : 0 ≤ α) (_hα' : α ≤ 17) (hfeas : c n α ^ 2 ≤ A n α) : R n α < 1 := by sorry
