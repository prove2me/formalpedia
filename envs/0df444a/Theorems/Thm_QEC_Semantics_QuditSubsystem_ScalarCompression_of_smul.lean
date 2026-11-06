-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_ScalarCompression_of_smul
-- name    : QEC.Semantics.QuditSubsystem.ScalarCompression.of_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:53:35.733873+00:00
-- url     : https://prove2.me/theorems/8cabcf85-fad8-4201-88ca-9c9b1b9bdc9d
-- title:
--   Scalar Compression: of smul
-- statement:
--   A nonzero scalar can be cancelled from a scalar compression.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L223-L238
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L223-L238

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

theorem QEC.Semantics.QuditSubsystem.ScalarCompression.of_smul
    {C : QuantumCode (Qudit.QuditRegister q)}
    {A : Operator (Qudit.QuditRegister q)} {a : Complex}
    (ha : a ≠ 0) (hA : ScalarCompression C (a • A)) : ScalarCompression C A := by sorry
