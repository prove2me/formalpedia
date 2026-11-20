-- Prove2me | Theorems.Thm_QEC_Distillation_BK05T_fiveQubitAcceptedOutput_tInputError
-- name    : QEC.Distillation.BK05T.fiveQubitAcceptedOutput_tInputError
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:44:57.071221+00:00
-- url     : https://prove2.me/theorems/8c7b5be2-b10d-4781-af3e-5327bb501798
-- title:
--   BK05 T: five Qubit Accepted Output t Input Error
-- statement:
--   The actual accepted density has exactly the analytic recurrence error.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Recurrence.lean#L165-L170
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Recurrence.lean#L165-L170

import Definitions.Def_QEC_Distillation_FiveQubitT_Postselection
import Definitions.Def_QEC_Distillation_FiveQubitT_Recurrence
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.BK05T
open Semantics Semantics.Qubit
open OneQubitMagic

theorem QEC.Distillation.BK05T.fiveQubitAcceptedOutput_tInputError
    (epsilon : Real) (hzero : 0 <= epsilon) (hhalf : epsilon <= 1 / 2) :
    tInputError (fiveQubitAcceptedOutput epsilon hzero (by linarith)) =
      bk05TRecurrence epsilon := by sorry
