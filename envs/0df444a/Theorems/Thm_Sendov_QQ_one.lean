-- Prove2me | Theorems.Thm_Sendov_QQ_one
-- name    : Sendov.QQ_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:54:16.435512+00:00
-- url     : https://prove2.me/theorems/1f59657f-6471-5829-ad0c-44880f07ab71
-- title:
--   Sendov: QQ one
-- statement:
--   The Sendov construction uses the QQ one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Common/Quadratic.lean#L54-L54
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Common/Quadratic.lean#L54-L54

import Definitions.Def_Sendov_Common_Rpow
import Definitions.Def_Sendov_Common_Quadratic
set_option autoImplicit false
open Sendov
variable {c A t : ℝ}

theorem Sendov.QQ_one (c A : ℝ) : QQ c A 1 = 1 - 2 * c + A := by sorry
