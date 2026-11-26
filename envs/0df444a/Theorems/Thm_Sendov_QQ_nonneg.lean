-- Prove2me | Theorems.Thm_Sendov_QQ_nonneg
-- name    : Sendov.QQ_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:55:14.089719+00:00
-- url     : https://prove2.me/theorems/1c2ce23b-c5e4-4d4c-bb12-01ae07287e2a
-- title:
--   Sendov: QQ nonneg
-- statement:
--   Feasibility `c² ≤ A` says exactly that `QQ` is a sum of squares.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Common/Quadratic.lean#L57-L59
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Common/Quadratic.lean#L57-L59

import Definitions.Def_Sendov_Common_Rpow
import Definitions.Def_Sendov_Common_Quadratic
set_option autoImplicit false
open Sendov
variable {c A t : ℝ}

theorem Sendov.QQ_nonneg (hfeas : c ^ 2 ≤ A) (t : ℝ) : 0 ≤ QQ c A t := by sorry
