-- Prove2me | Theorems.Thm_QEC_Distillation_BK05T_bk05TFidelityError_lt_threshold_iff
-- name    : QEC.Distillation.BK05T.bk05TFidelityError_lt_threshold_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:49:59.571832+00:00
-- url     : https://prove2.me/theorems/5a3d9e41-3de4-499b-9670-45b86114ee21
-- title:
--   BK05 T: bk05 TFidelity Error lt threshold iff
-- statement:
--   The analytic error threshold is exactly the source square-root fidelity
--   threshold, with no silent squaring of the public fidelity API.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Recurrence.lean#L629-L639
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Recurrence.lean#L629-L639

import Definitions.Def_QEC_Distillation_FiveQubitT_Postselection
import Definitions.Def_QEC_Distillation_FiveQubitT_Recurrence
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.BK05T
open Semantics Semantics.Qubit
open OneQubitMagic

theorem QEC.Distillation.BK05T.bk05TFidelityError_lt_threshold_iff
    (rho : DensityOperator QubitSpace) :
    bk05TFidelityError rho < bk05TThreshold <->
      bk05TFidelityThreshold < tFidelity rho := by sorry
