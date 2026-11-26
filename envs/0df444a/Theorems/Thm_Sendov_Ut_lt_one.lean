-- Prove2me | Theorems.Thm_Sendov_Ut_lt_one
-- name    : Sendov.Ut_lt_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:48:50.140162+00:00
-- url     : https://prove2.me/theorems/f3872548-469c-58c9-908d-720cca8181b5
-- title:
--   Sendov: Ut lt one
-- statement:
--   **The bound in `α` alone is below `1`.**
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/LargeDegree/Endgame.lean#L186-L248
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/LargeDegree/Endgame.lean#L186-L248

import Definitions.Def_Sendov_LargeDegree_Monotone
import Definitions.Def_Sendov_LargeDegree_Endgame
set_option autoImplicit false
open Sendov
variable {α : ℝ}
set_option maxHeartbeats 4000000

theorem Sendov.Ut_lt_one (hα : 0 ≤ α) (hα' : α ≤ 17) : Ut α < 1 := by sorry
