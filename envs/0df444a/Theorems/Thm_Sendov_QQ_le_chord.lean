-- Prove2me | Theorems.Thm_Sendov_QQ_le_chord
-- name    : Sendov.QQ_le_chord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:55:24.39308+00:00
-- url     : https://prove2.me/theorems/0d33b71a-5a81-45e0-bb8c-a21af54e798b
-- title:
--   Sendov: QQ le chord
-- statement:
--   Below the vertex, `QQ` lies under the chord `1 - ct`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Common/Quadratic.lean#L73-L75
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Common/Quadratic.lean#L73-L75

import Definitions.Def_Sendov_Common_Rpow
import Definitions.Def_Sendov_Common_Quadratic
set_option autoImplicit false
open Sendov
variable {c A t : ℝ}

theorem Sendov.QQ_le_chord (ht0 : 0 ≤ t) (ht : A * t ≤ c) : QQ c A t ≤ 1 - c * t := by sorry
