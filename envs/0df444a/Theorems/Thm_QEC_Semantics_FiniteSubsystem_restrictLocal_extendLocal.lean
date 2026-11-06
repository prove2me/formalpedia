-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteSubsystem_restrictLocal_extendLocal
-- name    : QEC.Semantics.FiniteSubsystem.restrictLocal_extendLocal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:12:00.206058+00:00
-- url     : https://prove2.me/theorems/37abe4aa-b08d-41fa-8ad3-335d37036608
-- title:
--   Finite Subsystem: restrict Local extend Local
-- statement:
--   Restriction is a left inverse to identity extension of local operators.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Subsystem.lean#L193-L201
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Subsystem.lean#L193-L201

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

theorem QEC.Semantics.FiniteSubsystem.restrictLocal_extendLocal (S : FiniteSubsystem ι) (A : Operator S.selectedSystem) :
    S.restrictLocal (S.extendLocal A) = A := by sorry
