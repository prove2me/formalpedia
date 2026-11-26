-- Prove2me | Theorems.Thm_Sendov_Q_eq_QQ
-- name    : Sendov.Q_eq_QQ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:56:27.205556+00:00
-- url     : https://prove2.me/theorems/2f50dff7-a0c3-5286-8793-4b2ef8cf34ec
-- title:
--   Sendov: Q eq QQ
-- statement:
--   `Sendov.Q` is an instance of `Sendov.QQ`.  Stated before the section variables below,
--   which deliberately shadow `Sendov.c` and `Sendov.A`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Common/Quadratic.lean#L44-L44
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Common/Quadratic.lean#L44-L44

import Definitions.Def_Sendov_Common_Rpow
import Definitions.Def_Sendov_Common_Quadratic
set_option autoImplicit false
open Sendov

theorem Sendov.Q_eq_QQ (n : ℕ) (α t : ℝ) : Q n α t = QQ (c n α) (A n α) t := by sorry
