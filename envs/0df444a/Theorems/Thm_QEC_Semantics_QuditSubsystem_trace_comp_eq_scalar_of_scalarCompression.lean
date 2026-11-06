-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_trace_comp_eq_scalar_of_scalarCompression
-- name    : QEC.Semantics.QuditSubsystem.trace_comp_eq_scalar_of_scalarCompression
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:53:19.227886+00:00
-- url     : https://prove2.me/theorems/67482e4d-ebbd-4ac6-98f3-d6f98b23fda6
-- title:
--   Qudit Subsystem: trace comp eq scalar of scalar Compression
-- statement:
--   A scalar compression fixes the trace of the operator against every encoded density.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L265-L305
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L265-L305

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

theorem QEC.Semantics.QuditSubsystem.trace_comp_eq_scalar_of_scalarCompression
    {C : QuantumCode (Qudit.QuditRegister q)} {A : Operator (Qudit.QuditRegister q)}
    {alpha : Complex}
    (hCompression : C.projector.comp (A.comp C.projector) = alpha • C.projector)
    (rho : DensityOperator (Qudit.QuditRegister q))
    (hRho : DensityOperator.SupportedOn C rho) :
    LinearMap.trace Complex (Qudit.QuditRegister q) (A.comp rho.toOperator) = alpha := by sorry
