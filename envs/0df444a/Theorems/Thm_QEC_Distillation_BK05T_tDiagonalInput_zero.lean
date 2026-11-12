-- Prove2me | Theorems.Thm_QEC_Distillation_BK05T_tDiagonalInput_zero
-- name    : QEC.Distillation.BK05T.tDiagonalInput_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:30:00.928886+00:00
-- url     : https://prove2.me/theorems/53e79920-47d9-4bea-99e3-17f120b0ce45
-- title:
--   BK05 T: t Diagonal Input zero
-- statement:
--   The diagonal density at `epsilon = 0` is exactly `T_0`; the vanishing
--   `T_1` raw branch is not replaced by an invented conditional state.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Input.lean#L116-L120
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Input.lean#L116-L120

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

theorem QEC.Distillation.BK05T.tDiagonalInput_zero :
    tDiagonalInput 0 (by norm_num) (by norm_num) = tZero := by sorry
