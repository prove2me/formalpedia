-- Prove2me | Theorems.Thm_Sendov_B36_37_finite_range
-- name    : Sendov.B36_37.finite_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:34:17.32845+00:00
-- url     : https://prove2.me/theorems/c29be809-d592-5a68-8194-151aa506a167
-- title:
--   B36 37: finite range
-- statement:
--   **The batch `36 ≤ n ≤ 37`.**
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree36_37.lean#L174-L201
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/FiniteRange/Degree36_37.lean#L174-L201

import Definitions.Def_Sendov_FiniteRange_Batch
import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Degree36_37
set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 4000000
open Sendov
open Sendov.B36_37
set_option maxHeartbeats 2000000

theorem Sendov.B36_37.finite_range {n : ℕ} (h0 : 36 ≤ n) (h1 : n ≤ 37) {α : ℝ}
    (hα : 0 ≤ α) (_hα' : α ≤ 17) (hfeas : c n α ^ 2 ≤ A n α) : R n α < 1 := by sorry
