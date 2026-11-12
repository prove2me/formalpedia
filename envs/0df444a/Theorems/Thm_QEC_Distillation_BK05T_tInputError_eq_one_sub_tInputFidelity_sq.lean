-- Prove2me | Theorems.Thm_QEC_Distillation_BK05T_tInputError_eq_one_sub_tInputFidelity_sq
-- name    : QEC.Distillation.BK05T.tInputError_eq_one_sub_tInputFidelity_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:23:01.06613+00:00
-- url     : https://prove2.me/theorems/29bb60ac-4e8e-4ad8-a6ca-76df27df192c
-- title:
--   BK05 T: t Input Error eq one sub t Input Fidelity sq
-- statement:
--   The source error parameter is tied to squared, not merely square-root,
--   fidelity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Input.lean#L262-L265
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Input.lean#L262-L265

import Definitions.Def_QEC_Distillation_Universality_OneQubitMagic
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Semantics_Entropy_Convexity
import Definitions.Def_QEC_Semantics_Instruments_Core
import Definitions.Def_QEC_Distillation_FiveQubitT_Input
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.BK05T
open Semantics Semantics.Qubit
open OneQubitMagic
open scoped BigOperators

theorem QEC.Distillation.BK05T.tInputError_eq_one_sub_tInputFidelity_sq
    (rho : DensityOperator QubitSpace) :
    tInputError rho = 1 - tInputFidelity rho ^ 2 := by sorry
