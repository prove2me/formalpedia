-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteSubsystem_supported_sub
-- name    : QEC.Semantics.FiniteSubsystem.supported_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:20:05.662139+00:00
-- url     : https://prove2.me/theorems/4deca3a0-9f15-4070-a303-8340948b7b1c
-- title:
--   Finite Subsystem: supported sub
-- statement:
--   The Finite Subsystem construction uses the supported sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/SubsystemOperatorAlgebra.lean#L79-L82
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/SubsystemOperatorAlgebra.lean#L79-L82

import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Semantics_Core_SubsystemOperatorAlgebra
set_option autoImplicit false
open QEC QEC.Semantics QEC.Semantics.FiniteSubsystem
open scoped TensorProduct BigOperators
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem QEC.Semantics.FiniteSubsystem.supported_sub (S : FiniteSubsystem ι) {A B : Operator (Qubit.QubitRegister ι)}
    (hA : S.OperatorSupportedOnRegister A) (hB : S.OperatorSupportedOnRegister B) :
    S.OperatorSupportedOnRegister (A-B) := by sorry
