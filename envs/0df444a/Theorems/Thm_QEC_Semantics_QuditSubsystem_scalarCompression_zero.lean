-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_scalarCompression_zero
-- name    : QEC.Semantics.QuditSubsystem.scalarCompression_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:17:10.177182+00:00
-- url     : https://prove2.me/theorems/203efa7b-b188-4e2a-9a0d-76dac60e8506
-- title:
--   Qudit Subsystem: scalar Compression zero
-- statement:
--   Scalar compression of the zero operator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L260-L262
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L260-L262

import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Semantics.QuditSubsystem
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {q : ι → Nat}

theorem QEC.Semantics.QuditSubsystem.scalarCompression_zero (C : QuantumCode (Qudit.QuditRegister q)) :
    ScalarCompression C (0 : Operator (Qudit.QuditRegister q)) := by sorry
