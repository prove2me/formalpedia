-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteSubsystem_extendLocalToRegister_add
-- name    : QEC.Semantics.FiniteSubsystem.extendLocalToRegister_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:19:17.061183+00:00
-- url     : https://prove2.me/theorems/741fcd87-bcfd-48b5-a6dc-993629faca7c
-- title:
--   Finite Subsystem: extend Local To Register add
-- statement:
--   The Finite Subsystem construction uses the extend Local To Register add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/SubsystemOperatorAlgebra.lean#L39-L43
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/SubsystemOperatorAlgebra.lean#L39-L43

import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Semantics_Core_SubsystemOperatorAlgebra
set_option autoImplicit false
open QEC QEC.Semantics QEC.Semantics.FiniteSubsystem
open scoped TensorProduct BigOperators
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem QEC.Semantics.FiniteSubsystem.extendLocalToRegister_add (S : FiniteSubsystem ι) (A B : Operator S.selectedSystem) :
    S.extendLocalToRegister (A+B) = S.extendLocalToRegister A + S.extendLocalToRegister B := by sorry
