-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_noInformationOn_iff_allLocalScalarCompression
-- name    : QEC.Semantics.QuditSubsystem.noInformationOn_iff_allLocalScalarCompression
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:49:23.757878+00:00
-- url     : https://prove2.me/theorems/60e41c06-c708-4bde-944e-df411d7d80d3
-- title:
--   Qudit Subsystem: no Information On iff all Local Scalar Compression
-- statement:
--   Valid-effect no-information is equivalent to scalar compression for all local operators.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L518-L535
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L518-L535

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

theorem QEC.Semantics.QuditSubsystem.noInformationOn_iff_allLocalScalarCompression
    (C : QuantumCode (Qudit.QuditRegister q)) (S : QuditSubsystem q) :
    NoInformationOn C S ↔ AllLocalScalarCompression C S := by sorry
