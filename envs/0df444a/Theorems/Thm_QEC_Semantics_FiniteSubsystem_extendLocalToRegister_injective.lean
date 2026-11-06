-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteSubsystem_extendLocalToRegister_injective
-- name    : QEC.Semantics.FiniteSubsystem.extendLocalToRegister_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:43:16.145839+00:00
-- url     : https://prove2.me/theorems/57de9bba-5053-4b27-993c-9f27d96c206d
-- title:
--   Finite Subsystem: extend Local To Register injective
-- statement:
--   Local extension to the global coordinate register is injective.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Subsystem.lean#L218-L222
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Subsystem.lean#L218-L222

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

theorem QEC.Semantics.FiniteSubsystem.extendLocalToRegister_injective (S : FiniteSubsystem ι) :
    Function.Injective S.extendLocalToRegister := by sorry
