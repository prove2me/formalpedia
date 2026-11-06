-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteSubsystem_supported_zero
-- name    : QEC.Semantics.FiniteSubsystem.supported_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:33:30.312851+00:00
-- url     : https://prove2.me/theorems/121dde6b-3617-48c6-ad1b-2987bd40b964
-- title:
--   Finite Subsystem: supported zero
-- statement:
--   The Finite Subsystem construction uses the supported zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/SubsystemOperatorAlgebra.lean#L64-L65
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/SubsystemOperatorAlgebra.lean#L64-L65

import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Semantics_Core_SubsystemOperatorAlgebra
set_option autoImplicit false
open QEC QEC.Semantics QEC.Semantics.FiniteSubsystem
open scoped TensorProduct BigOperators
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem QEC.Semantics.FiniteSubsystem.supported_zero (S : FiniteSubsystem ι) : S.OperatorSupportedOnRegister 0 := by sorry
