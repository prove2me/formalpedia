-- Prove2me | Theorems.Thm_QEC_Distillation_BK05T_tZero_tOne_orthogonal
-- name    : QEC.Distillation.BK05T.tZero_tOne_orthogonal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:21:50.056352+00:00
-- url     : https://prove2.me/theorems/c3d04f36-b0b3-4708-972f-f3c38a5dee22
-- title:
--   BK05 T: t Zero t One orthogonal
-- statement:
--   The two source components are orthogonal rank-one density operators.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Input.lean#L139-L152
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Input.lean#L139-L152

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

theorem QEC.Distillation.BK05T.tZero_tOne_orthogonal : tZero.toOperator * tOne.toOperator = 0 := by sorry
