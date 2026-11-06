-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_ScalarCompression_add
-- name    : QEC.Semantics.QuditSubsystem.ScalarCompression.add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:49:34.80943+00:00
-- url     : https://prove2.me/theorems/525a3747-4a7e-4be1-997e-0f21262cc716
-- title:
--   Scalar Compression: add
-- statement:
--   Scalar compression is closed under addition.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L241-L246
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L241-L246

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

theorem QEC.Semantics.QuditSubsystem.ScalarCompression.add
    {C : QuantumCode (Qudit.QuditRegister q)}
    {A B : Operator (Qudit.QuditRegister q)}
    (hA : ScalarCompression C A) (hB : ScalarCompression C B) :
    ScalarCompression C (A + B) := by sorry
