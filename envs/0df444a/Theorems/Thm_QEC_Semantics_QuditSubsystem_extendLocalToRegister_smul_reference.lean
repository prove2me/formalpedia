-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_extendLocalToRegister_smul_reference
-- name    : QEC.Semantics.QuditSubsystem.extendLocalToRegister_smul_reference
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:20:02.535782+00:00
-- url     : https://prove2.me/theorems/0c8cbbdd-ea53-4089-9d55-2ef93bc3ba59
-- title:
--   Qudit Subsystem: extend Local To Register smul reference
-- statement:
--   The Qudit Subsystem construction uses the extend Local To Register smul reference property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/ReferenceDecoupling.lean#L573-L579
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/ReferenceDecoupling.lean#L573-L579

import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Entropy_MatrixRelative
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_ReferenceDecoupling
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open Classical
open DensityOperator
open scoped BigOperators ComplexOrder TensorProduct
universe u v w
open QEC.Semantics.QuditSubsystem
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {q : ι → Nat}

theorem QEC.Semantics.QuditSubsystem.extendLocalToRegister_smul_reference (S : QuditSubsystem q) (a : Complex)
    (A : Operator S.selectedSystem) :
    S.extendLocalToRegister (a • A) = a • S.extendLocalToRegister A := by sorry
