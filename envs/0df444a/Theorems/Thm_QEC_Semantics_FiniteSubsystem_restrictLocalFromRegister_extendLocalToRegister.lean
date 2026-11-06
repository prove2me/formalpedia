-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteSubsystem_restrictLocalFromRegister_extendLocalToRegister
-- name    : QEC.Semantics.FiniteSubsystem.restrictLocalFromRegister_extendLocalToRegister
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:12:50.960196+00:00
-- url     : https://prove2.me/theorems/999bc9ce-df41-4e05-8340-0467a807bbf5
-- title:
--   Finite Subsystem: restrict Local From Register extend Local To Register
-- statement:
--   Global-register restriction is a left inverse to local extension.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Subsystem.lean#L204-L209
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Subsystem.lean#L204-L209

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

theorem QEC.Semantics.FiniteSubsystem.restrictLocalFromRegister_extendLocalToRegister (S : FiniteSubsystem ι)
    (A : Operator S.selectedSystem) :
    S.restrictLocalFromRegister (S.extendLocalToRegister A) = A := by sorry
