-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_scalarCompression_iff_detectableOn
-- name    : QEC.Semantics.QuditSubsystem.scalarCompression_iff_detectableOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:49:24.729506+00:00
-- url     : https://prove2.me/theorems/7557540c-92a2-448b-a0b8-81a955ccbb0a
-- title:
--   Qudit Subsystem: scalar Compression iff detectable On
-- statement:
--   Scalar compression is precisely the existing carrier-matrix-element detectability notion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L183-L187
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L183-L187

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

theorem QEC.Semantics.QuditSubsystem.scalarCompression_iff_detectableOn (C : QuantumCode (Qudit.QuditRegister q))
    (A : Operator (Qudit.QuditRegister q)) :
    ScalarCompression C A ↔ DetectableOn C A := by sorry
