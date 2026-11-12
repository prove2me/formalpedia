-- Prove2me | Theorems.Thm_QEC_Distillation_BK05T_tTwirl_eq_diagonalInput_of_inputError
-- name    : QEC.Distillation.BK05T.tTwirl_eq_diagonalInput_of_inputError
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:21:42.483165+00:00
-- url     : https://prove2.me/theorems/9d8a3f7a-f283-4d68-bbb0-6eb4aa56715b
-- title:
--   BK05 T: t Twirl eq diagonal Input of input Error
-- statement:
--   Every one-qubit density is diagonalized by the physical twirl at its
--   actual measured input error; no caller-supplied diagonalization premise is
--   needed.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Input.lean#L597-L604
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Input.lean#L597-L604

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

theorem QEC.Distillation.BK05T.tTwirl_eq_diagonalInput_of_inputError
    (rho : DensityOperator QubitSpace)
    (hzero : 0 ≤ tInputError rho) (hone : tInputError rho ≤ 1) :
    tTwirl rho = tDiagonalInput (tInputError rho) hzero hone := by sorry
