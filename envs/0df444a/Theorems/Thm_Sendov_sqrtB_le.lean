-- Prove2me | Theorems.Thm_Sendov_sqrtB_le
-- name    : Sendov.sqrtB_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T18:08:19.337989+00:00
-- url     : https://prove2.me/theorems/239b119e-007a-5a06-96c3-775dcda1175c
-- title:
--   Sendov: sqrt B le
-- statement:
--   `√B ≤ 12/13` on `0 ≤ α ≤ 17`, since `B ≤ 17/20 ≤ (12/13)²`.  A rational bound is enough
--   here, and avoids carrying a square root into the step ratio.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/LargeDegree/Monotone.lean#L237-L245
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/LargeDegree/Monotone.lean#L237-L245

import Definitions.Def_Sendov_LargeDegree_Tail
import Definitions.Def_Sendov_LargeDegree_Monotone
set_option autoImplicit false
open Sendov
variable {n : ℕ} {α : ℝ}

theorem Sendov.sqrtB_le (hα : 0 ≤ α) (hα' : α ≤ 17) : Real.sqrt (α / (3 + α)) ≤ 12 / 13 := by sorry
