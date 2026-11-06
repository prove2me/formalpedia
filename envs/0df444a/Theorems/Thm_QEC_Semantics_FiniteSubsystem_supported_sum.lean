-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteSubsystem_supported_sum
-- name    : QEC.Semantics.FiniteSubsystem.supported_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:44:07.206341+00:00
-- url     : https://prove2.me/theorems/84210dc4-30b7-4ade-8771-b09b0183522d
-- title:
--   Finite Subsystem: supported sum
-- statement:
--   The Finite Subsystem construction uses the supported sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/SubsystemOperatorAlgebra.lean#L89-L98
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/SubsystemOperatorAlgebra.lean#L89-L98

import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Semantics_Core_SubsystemOperatorAlgebra
set_option autoImplicit false
open QEC QEC.Semantics QEC.Semantics.FiniteSubsystem
open scoped TensorProduct BigOperators
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem QEC.Semantics.FiniteSubsystem.supported_sum (S : FiniteSubsystem ι) {κ : Type*} (s : Finset κ)
    (A : κ → Operator (Qubit.QubitRegister ι))
    (h : ∀ k ∈ s, S.OperatorSupportedOnRegister (A k)) :
    S.OperatorSupportedOnRegister (∑ k ∈ s, A k) := by sorry
