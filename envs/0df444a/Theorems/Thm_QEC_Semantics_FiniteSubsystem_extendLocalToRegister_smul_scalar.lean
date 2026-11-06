-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteSubsystem_extendLocalToRegister_smul_scalar
-- name    : QEC.Semantics.FiniteSubsystem.extendLocalToRegister_smul_scalar
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:19:32.383652+00:00
-- url     : https://prove2.me/theorems/0e79734c-cdd6-4ba0-a69a-8da55e983116
-- title:
--   Finite Subsystem: extend Local To Register smul scalar
-- statement:
--   The Finite Subsystem construction uses the extend Local To Register smul scalar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/SubsystemOperatorAlgebra.lean#L45-L50
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/SubsystemOperatorAlgebra.lean#L45-L50

import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Semantics_Core_SubsystemOperatorAlgebra
set_option autoImplicit false
open QEC QEC.Semantics QEC.Semantics.FiniteSubsystem
open scoped TensorProduct BigOperators
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem QEC.Semantics.FiniteSubsystem.extendLocalToRegister_smul_scalar (S : FiniteSubsystem ι) (c : ℂ)
    (A : Operator S.selectedSystem) :
    S.extendLocalToRegister (c • A) = c • S.extendLocalToRegister A := by sorry
