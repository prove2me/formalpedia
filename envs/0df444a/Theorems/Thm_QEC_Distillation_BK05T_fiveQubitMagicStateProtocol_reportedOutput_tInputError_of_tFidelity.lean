-- Prove2me | Theorems.Thm_QEC_Distillation_BK05T_fiveQubitMagicStateProtocol_reportedOutput_tInputError_of_tFidelity
-- name    : QEC.Distillation.BK05T.fiveQubitMagicStateProtocol_reportedOutput_tInputError_of_tFidelity
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T07:42:58.983601+00:00
-- url     : https://prove2.me/theorems/1878c5c8-e902-49d0-9ac8-f3049e3c800d
-- title:
--   BK05 T: five Qubit Magic State Protocol reported Output t Input Error of t Fidelity
-- statement:
--   Under the exact square-root fidelity hypothesis, the concrete protocol's
--   reported accepted density has the source recurrence error.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Recurrence.lean#L643-L657
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Recurrence.lean#L643-L657

import Definitions.Def_QEC_Distillation_FiveQubitT_Postselection
import Definitions.Def_QEC_Distillation_FiveQubitT_Recurrence
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.BK05T
open Semantics Semantics.Qubit
open OneQubitMagic

theorem QEC.Distillation.BK05T.fiveQubitMagicStateProtocol_reportedOutput_tInputError_of_tFidelity
    (rho : DensityOperator QubitSpace)
    (hfidelity : bk05TFidelityThreshold < tFidelity rho) :
    tInputError
        ((fiveQubitMagicStateProtocol (bk05TFidelityError rho)
          (bk05TFidelityError_nonneg rho) (bk05TFidelityError_le_one rho)).run.reportedOutput
          (fiveQubitMagicStateProtocol (bk05TFidelityError rho)
            (bk05TFidelityError_nonneg rho)
            (bk05TFidelityError_le_one rho)).behavior) =
      bk05TRecurrence (bk05TFidelityError rho) := by sorry
