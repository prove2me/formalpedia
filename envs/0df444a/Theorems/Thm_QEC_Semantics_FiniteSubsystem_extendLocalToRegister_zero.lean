-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteSubsystem_extendLocalToRegister_zero
-- name    : QEC.Semantics.FiniteSubsystem.extendLocalToRegister_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:17:09.888282+00:00
-- url     : https://prove2.me/theorems/57bcafbc-1e3c-451a-a1c4-3402d0bb3359
-- title:
--   Finite Subsystem: extend Local To Register zero
-- statement:
--   The Finite Subsystem construction uses the extend Local To Register zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/SubsystemOperatorAlgebra.lean#L33-L37
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/SubsystemOperatorAlgebra.lean#L33-L37

import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Semantics_Core_SubsystemOperatorAlgebra
set_option autoImplicit false
open QEC QEC.Semantics QEC.Semantics.FiniteSubsystem
open scoped TensorProduct BigOperators
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem QEC.Semantics.FiniteSubsystem.extendLocalToRegister_zero (S : FiniteSubsystem ι) :
    S.extendLocalToRegister 0 = 0 := by sorry
