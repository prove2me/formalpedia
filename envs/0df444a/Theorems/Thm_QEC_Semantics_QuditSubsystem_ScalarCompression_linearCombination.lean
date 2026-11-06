-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_ScalarCompression_linearCombination
-- name    : QEC.Semantics.QuditSubsystem.ScalarCompression.linearCombination
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:53:33.879931+00:00
-- url     : https://prove2.me/theorems/6208a8c5-e52b-400d-bef8-8fed957bcf3c
-- title:
--   Scalar Compression: linear Combination
-- statement:
--   Scalar compression is closed under complex linear combinations.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L190-L206
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L190-L206

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

theorem QEC.Semantics.QuditSubsystem.ScalarCompression.linearCombination
    {C : QuantumCode (Qudit.QuditRegister q)}
    {A B : Operator (Qudit.QuditRegister q)}
    (hA : ScalarCompression C A) (hB : ScalarCompression C B)
    (a b : Complex) : ScalarCompression C (a • A + b • B) := by sorry
