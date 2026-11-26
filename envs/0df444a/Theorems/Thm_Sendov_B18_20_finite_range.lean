-- Prove2me | Theorems.Thm_Sendov_B18_20_finite_range
-- name    : Sendov.B18_20.finite_range
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T18:26:13.687521+00:00
-- url     : https://prove2.me/theorems/309c4166-3fa6-5077-a5f3-3e50e2573945
-- title:
--   B18 20: finite range
-- statement:
--   **The batch `18 ≤ n ≤ 20`.**
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree18_20.lean#L138-L165
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree18_20.lean#L138-L165

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree18_20
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B18_20
set_option maxHeartbeats 2000000

theorem Sendov.B18_20.finite_range {n : ℕ} (h0 : 18 ≤ n) (h1 : n ≤ 20) {α : ℝ}
    (hα : 0 ≤ α) (_hα' : α ≤ 17) (hfeas : c n α ^ 2 ≤ A n α) : R n α < 1 := by sorry
