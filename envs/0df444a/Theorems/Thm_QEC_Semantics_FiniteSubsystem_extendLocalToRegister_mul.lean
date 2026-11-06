-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteSubsystem_extendLocalToRegister_mul
-- name    : QEC.Semantics.FiniteSubsystem.extendLocalToRegister_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:19:36.972352+00:00
-- url     : https://prove2.me/theorems/03158b58-b180-4f1c-ac28-9d967c54b55f
-- title:
--   Finite Subsystem: extend Local To Register mul
-- statement:
--   The Finite Subsystem construction uses the extend Local To Register mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/SubsystemOperatorAlgebra.lean#L52-L54
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/SubsystemOperatorAlgebra.lean#L52-L54

import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Semantics_Core_SubsystemOperatorAlgebra
set_option autoImplicit false
open QEC QEC.Semantics QEC.Semantics.FiniteSubsystem
open scoped TensorProduct BigOperators
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem QEC.Semantics.FiniteSubsystem.extendLocalToRegister_mul (S : FiniteSubsystem ι) (A B : Operator S.selectedSystem) :
    S.extendLocalToRegister (A*B) = S.extendLocalToRegister A * S.extendLocalToRegister B := by sorry
