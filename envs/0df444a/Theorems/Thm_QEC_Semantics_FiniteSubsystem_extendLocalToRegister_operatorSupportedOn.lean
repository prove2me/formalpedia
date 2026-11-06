-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteSubsystem_extendLocalToRegister_operatorSupportedOn
-- name    : QEC.Semantics.FiniteSubsystem.extendLocalToRegister_operatorSupportedOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:43:18.581986+00:00
-- url     : https://prove2.me/theorems/be2009ff-2bce-409a-93b9-a337e9e0e54b
-- title:
--   Finite Subsystem: extend Local To Register operator Supported On
-- statement:
--   The Finite Subsystem construction uses the extend Local To Register operator Supported On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Subsystem.lean#L238-L241
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Subsystem.lean#L238-L241

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Semantics_Core_Subsystem
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u
open QEC.Semantics.FiniteSubsystem
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Semantics.FiniteSubsystem.extendLocalToRegister_operatorSupportedOn (S : FiniteSubsystem ι)
    (A : Operator S.selectedSystem) :
    S.OperatorSupportedOnRegister (S.extendLocalToRegister A) := by sorry
