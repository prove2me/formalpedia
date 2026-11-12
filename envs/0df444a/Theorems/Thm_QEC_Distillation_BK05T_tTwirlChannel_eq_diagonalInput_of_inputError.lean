-- Prove2me | Theorems.Thm_QEC_Distillation_BK05T_tTwirlChannel_eq_diagonalInput_of_inputError
-- name    : QEC.Distillation.BK05T.tTwirlChannel_eq_diagonalInput_of_inputError
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T14:33:04.983254+00:00
-- url     : https://prove2.me/theorems/f1b0dec7-455a-4ef3-86a4-97aeb915eb9c
-- title:
--   BK05 T: t Twirl Channel eq diagonal Input of input Error
-- statement:
--   The same assumption-free diagonalization bridge for the finite-Kraus
--   CPTP channel.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Input.lean#L608-L614
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FiveQubitT/Input.lean#L608-L614

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

theorem QEC.Distillation.BK05T.tTwirlChannel_eq_diagonalInput_of_inputError
    (rho : DensityOperator QubitSpace)
    (hzero : 0 ≤ tInputError rho) (hone : tInputError rho ≤ 1) :
    tTwirlChannel.mapDensity rho =
      tDiagonalInput (tInputError rho) hzero hone := by sorry
