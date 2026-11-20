-- Prove2me | Theorems.Thm_QEC_Distillation_BK05T_fiveQubitAcceptedOutput_eq_diagonalInput
-- name    : QEC.Distillation.BK05T.fiveQubitAcceptedOutput_eq_diagonalInput
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:41:47.424189+00:00
-- url     : https://prove2.me/theorems/3c1a3a51-26ed-4141-9c21-d77a5874d4c8
-- title:
--   BK05 T: five Qubit Accepted Output eq diagonal Input
-- statement:
--   The normalized physical accepted density is the diagonal input whose error
--   parameter is the recurrence value.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Recurrence.lean#L142-L162
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Recurrence.lean#L142-L162

import Definitions.Def_QEC_Distillation_FiveQubitT_Postselection
import Definitions.Def_QEC_Distillation_FiveQubitT_Recurrence
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.BK05T
open Semantics Semantics.Qubit
open OneQubitMagic

theorem QEC.Distillation.BK05T.fiveQubitAcceptedOutput_eq_diagonalInput
    (epsilon : Real) (hzero : 0 <= epsilon) (hhalf : epsilon <= 1 / 2) :
    fiveQubitAcceptedOutput epsilon hzero (by linarith) =
      tDiagonalInput (bk05TRecurrence epsilon)
        (bk05TRecurrence_nonneg epsilon hzero hhalf)
        ((bk05TRecurrence_le_half epsilon hzero hhalf).trans (by norm_num)) := by sorry
