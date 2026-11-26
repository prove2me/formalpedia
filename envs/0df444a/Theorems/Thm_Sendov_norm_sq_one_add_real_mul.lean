-- Prove2me | Theorems.Thm_Sendov_norm_sq_one_add_real_mul
-- name    : Sendov.norm_sq_one_add_real_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:55:35.981347+00:00
-- url     : https://prove2.me/theorems/edf02110-f064-5be1-b541-f28eb151a7bb
-- title:
--   Sendov: norm sq one add real mul
-- statement:
--   `‖1 + s v‖² = 1 + 2 s Re v + s² ‖v‖²` for real `s`.
--
--   Source: https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/Origin.lean#L90-L95
-- source:
--   https://github.com/teorth/sendov/blob/1ddea92d89f951a0a7cbbffa6c267cf7e6640b1d/Sendov/Analytic/Origin.lean#L90-L95

import Definitions.Def_Sendov_Counterexample_Identities
import Definitions.Def_Sendov_Analytic_Maclaurin
import Definitions.Def_Sendov_Analytic_Defect
import Definitions.Def_Sendov_Common_Quadratic
import Definitions.Def_Sendov_Analytic_Polar
import Definitions.Def_Sendov_Analytic_Origin
set_option autoImplicit false
open Sendov

theorem Sendov.norm_sq_one_add_real_mul (s : ℝ) (v : ℂ) :
    ‖1 + (s : ℂ) * v‖ ^ 2 = 1 + 2 * s * v.re + s ^ 2 * ‖v‖ ^ 2 := by sorry
