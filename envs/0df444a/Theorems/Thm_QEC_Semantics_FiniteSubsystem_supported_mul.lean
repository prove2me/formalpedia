-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteSubsystem_supported_mul
-- name    : QEC.Semantics.FiniteSubsystem.supported_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:20:07.578798+00:00
-- url     : https://prove2.me/theorems/70873543-dec8-4424-a85d-ca7799625d9c
-- title:
--   Finite Subsystem: supported mul
-- statement:
--   The Finite Subsystem construction uses the supported mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/SubsystemOperatorAlgebra.lean#L83-L88
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/SubsystemOperatorAlgebra.lean#L83-L88

import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Semantics_Core_SubsystemOperatorAlgebra
set_option autoImplicit false
open QEC QEC.Semantics QEC.Semantics.FiniteSubsystem
open scoped TensorProduct BigOperators
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem QEC.Semantics.FiniteSubsystem.supported_mul (S : FiniteSubsystem ι) {A B : Operator (Qubit.QubitRegister ι)}
    (hA : S.OperatorSupportedOnRegister A) (hB : S.OperatorSupportedOnRegister B) :
    S.OperatorSupportedOnRegister (A*B) := by sorry
