-- Prove2me | Theorems.Thm_QEC_Distillation_BK05T_tOne_tZero_orthogonal
-- name    : QEC.Distillation.BK05T.tOne_tZero_orthogonal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:30:04.589125+00:00
-- url     : https://prove2.me/theorems/a3ae4c2f-1d63-490f-9a38-4a21e90081d1
-- title:
--   BK05 T: t One t Zero orthogonal
-- statement:
--   Orthogonality also holds in the opposite operator order.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Input.lean#L155-L168
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Input.lean#L155-L168

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

theorem QEC.Distillation.BK05T.tOne_tZero_orthogonal : tOne.toOperator * tZero.toOperator = 0 := by sorry
