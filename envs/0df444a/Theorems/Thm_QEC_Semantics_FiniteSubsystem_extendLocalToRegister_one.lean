-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteSubsystem_extendLocalToRegister_one
-- name    : QEC.Semantics.FiniteSubsystem.extendLocalToRegister_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:17:25.994245+00:00
-- url     : https://prove2.me/theorems/16f4e333-71e7-483e-8318-4db66e9ee2bc
-- title:
--   Finite Subsystem: extend Local To Register one
-- statement:
--   The Finite Subsystem construction uses the extend Local To Register one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/SubsystemOperatorAlgebra.lean#L56-L62
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/SubsystemOperatorAlgebra.lean#L56-L62

import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Semantics_Core_SubsystemOperatorAlgebra
set_option autoImplicit false
open QEC QEC.Semantics QEC.Semantics.FiniteSubsystem
open scoped TensorProduct BigOperators
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem QEC.Semantics.FiniteSubsystem.extendLocalToRegister_one (S : FiniteSubsystem ι) :
    S.extendLocalToRegister 1 = 1 := by sorry
