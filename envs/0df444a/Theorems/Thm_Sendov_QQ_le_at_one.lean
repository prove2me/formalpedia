-- Prove2me | Theorems.Thm_Sendov_QQ_le_at_one
-- name    : Sendov.QQ_le_at_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:55:32.425307+00:00
-- url     : https://prove2.me/theorems/3bbd3183-4811-45d7-bf53-26a706fa5334
-- title:
--   Sendov: QQ le at one
-- statement:
--   Above the vertex, `QQ` is increasing, so it is at most its value at `t = 1`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Common/Quadratic.lean#L78-L81
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Common/Quadratic.lean#L78-L81

import Definitions.Def_Sendov_Common_Rpow
import Definitions.Def_Sendov_Common_Quadratic
set_option autoImplicit false
open Sendov
variable {c A t : ℝ}

theorem Sendov.QQ_le_at_one (hA : 0 ≤ A) (ht : c ≤ A * t) (ht1 : t ≤ 1) : QQ c A t ≤ QQ c A 1 := by sorry
