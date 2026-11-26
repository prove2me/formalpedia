-- Prove2me | Theorems.Thm_Sendov_QQ_eq
-- name    : Sendov.QQ_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:54:26.203661+00:00
-- url     : https://prove2.me/theorems/4760ff89-c3a7-4417-99a8-e3f2e4f138f4
-- title:
--   Sendov: QQ eq
-- statement:
--   `QQ` as a sum of squares.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Common/Quadratic.lean#L49-L50
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Common/Quadratic.lean#L49-L50

import Definitions.Def_Sendov_Common_Rpow
import Definitions.Def_Sendov_Common_Quadratic
set_option autoImplicit false
open Sendov
variable {c A t : ℝ}

theorem Sendov.QQ_eq (c A t : ℝ) : QQ c A t = (1 - c * t) ^ 2 + (A - c ^ 2) * t ^ 2 := by sorry
