-- Prove2me | Theorems.Thm_QEC_Distillation_BK05T_tCanonicalizedInput_error_eq_bk05TFidelityError
-- name    : QEC.Distillation.BK05T.tCanonicalizedInput_error_eq_bk05TFidelityError
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:44:25.577816+00:00
-- url     : https://prove2.me/theorems/fee480ab-2bf6-41d4-a6ce-5a7757014ce9
-- title:
--   BK05 T: t Canonicalized Input error eq bk05 TFidelity Error
-- statement:
--   Finite-Clifford canonicalization ties the analytic error to actual maximum
--   square-root fidelity, without replacing `tFidelity` by a squared convention.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Recurrence.lean#L458-L461
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Recurrence.lean#L458-L461

import Definitions.Def_QEC_Distillation_FiveQubitT_Postselection
import Definitions.Def_QEC_Distillation_FiveQubitT_Recurrence
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.BK05T
open Semantics Semantics.Qubit
open OneQubitMagic

theorem QEC.Distillation.BK05T.tCanonicalizedInput_error_eq_bk05TFidelityError
    (rho : DensityOperator QubitSpace) :
    tInputError (tCanonicalizedInput rho) = bk05TFidelityError rho := by sorry
