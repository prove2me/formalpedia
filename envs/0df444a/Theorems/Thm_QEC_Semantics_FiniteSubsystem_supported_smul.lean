-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteSubsystem_supported_smul
-- name    : QEC.Semantics.FiniteSubsystem.supported_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:48:02.398212+00:00
-- url     : https://prove2.me/theorems/f59da516-322a-4e0d-bf98-f9960c2e95e5
-- title:
--   Finite Subsystem: supported smul
-- statement:
--   The Finite Subsystem construction uses the supported smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/SubsystemOperatorAlgebra.lean#L74-L78
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/SubsystemOperatorAlgebra.lean#L74-L78

import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Semantics_Core_SubsystemOperatorAlgebra
set_option autoImplicit false
open QEC QEC.Semantics QEC.Semantics.FiniteSubsystem
open scoped TensorProduct BigOperators
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem QEC.Semantics.FiniteSubsystem.supported_smul (S : FiniteSubsystem ι) (c : ℂ)
    {A : Operator (Qubit.QubitRegister ι)} (hA : S.OperatorSupportedOnRegister A) :
    S.OperatorSupportedOnRegister (c • A) := by sorry
