-- Prove2me | Theorems.Thm_Sendov_QQ_le_one
-- name    : Sendov.QQ_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:56:48.448864+00:00
-- url     : https://prove2.me/theorems/43569669-f4ae-454d-b595-2dd67fc165e4
-- title:
--   Sendov: QQ le one
-- statement:
--   `QQ ≤ 1` on `[0,1]`, from `QQ 1 ≤ 1` and `0 ≤ c` alone.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Common/Quadratic.lean#L62-L70
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Common/Quadratic.lean#L62-L70

import Definitions.Def_Sendov_Common_Rpow
import Definitions.Def_Sendov_Common_Quadratic
set_option autoImplicit false
open Sendov
variable {c A t : ℝ}

theorem Sendov.QQ_le_one (hc : 0 ≤ c) (hB : QQ c A 1 ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    QQ c A t ≤ 1 := by sorry
