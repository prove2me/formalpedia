-- Prove2me | Theorems.Thm_QEC_Distillation_BK05T_tZero_idempotent
-- name    : QEC.Distillation.BK05T.tZero_idempotent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:21:37.830287+00:00
-- url     : https://prove2.me/theorems/75f67422-b07b-4a58-b6b7-1d3ea99e8275
-- title:
--   BK05 T: t Zero idempotent
-- statement:
--   The ideal T0 density is its rank-one projector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Input.lean#L178-L181
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Input.lean#L178-L181

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

theorem QEC.Distillation.BK05T.tZero_idempotent : tZero.toOperator * tZero.toOperator = tZero.toOperator := by sorry
