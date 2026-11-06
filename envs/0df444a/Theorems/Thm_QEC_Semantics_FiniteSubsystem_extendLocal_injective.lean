-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteSubsystem_extendLocal_injective
-- name    : QEC.Semantics.FiniteSubsystem.extendLocal_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:43:14.762618+00:00
-- url     : https://prove2.me/theorems/0f9a9bd7-d2bb-4b27-bfef-8d80e3cbbc33
-- title:
--   Finite Subsystem: extend Local injective
-- statement:
--   Identity extension of local operators is injective.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Subsystem.lean#L212-L215
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Subsystem.lean#L212-L215

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

theorem QEC.Semantics.FiniteSubsystem.extendLocal_injective (S : FiniteSubsystem ι) : Function.Injective S.extendLocal := by sorry
