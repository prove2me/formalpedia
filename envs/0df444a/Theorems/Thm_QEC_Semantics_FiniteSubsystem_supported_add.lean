-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteSubsystem_supported_add
-- name    : QEC.Semantics.FiniteSubsystem.supported_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:37:59.353818+00:00
-- url     : https://prove2.me/theorems/2e41764f-ea66-4b20-9fbd-5a7bcf9b979d
-- title:
--   Finite Subsystem: supported add
-- statement:
--   The Finite Subsystem construction uses the supported add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/SubsystemOperatorAlgebra.lean#L68-L73
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/SubsystemOperatorAlgebra.lean#L68-L73

import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Semantics_Core_SubsystemOperatorAlgebra
set_option autoImplicit false
open QEC QEC.Semantics QEC.Semantics.FiniteSubsystem
open scoped TensorProduct BigOperators
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem QEC.Semantics.FiniteSubsystem.supported_add (S : FiniteSubsystem ι) {A B : Operator (Qubit.QubitRegister ι)}
    (hA : S.OperatorSupportedOnRegister A) (hB : S.OperatorSupportedOnRegister B) :
    S.OperatorSupportedOnRegister (A+B) := by sorry
