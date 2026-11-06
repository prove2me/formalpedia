-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteSubsystem_supported_one
-- name    : QEC.Semantics.FiniteSubsystem.supported_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:44:04.255697+00:00
-- url     : https://prove2.me/theorems/6d68e049-ad86-46a7-8d57-d462ba0eb9e6
-- title:
--   Finite Subsystem: supported one
-- statement:
--   The Finite Subsystem construction uses the supported one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/SubsystemOperatorAlgebra.lean#L66-L67
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/SubsystemOperatorAlgebra.lean#L66-L67

import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Semantics_Core_SubsystemOperatorAlgebra
set_option autoImplicit false
open QEC QEC.Semantics QEC.Semantics.FiniteSubsystem
open scoped TensorProduct BigOperators
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem QEC.Semantics.FiniteSubsystem.supported_one (S : FiniteSubsystem ι) : S.OperatorSupportedOnRegister 1 := by sorry
