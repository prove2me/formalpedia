-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_ScalarCompression_smul
-- name    : QEC.Semantics.QuditSubsystem.ScalarCompression.smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:49:43.469956+00:00
-- url     : https://prove2.me/theorems/53bdfc15-9866-4306-89c5-76ffe24a2cbd
-- title:
--   Scalar Compression: smul
-- statement:
--   Scalar compression is closed under complex scaling.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L209-L220
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L209-L220

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

theorem QEC.Semantics.QuditSubsystem.ScalarCompression.smul
    {C : QuantumCode (Qudit.QuditRegister q)}
    {A : Operator (Qudit.QuditRegister q)}
    (hA : ScalarCompression C A) (a : Complex) : ScalarCompression C (a • A) := by sorry
