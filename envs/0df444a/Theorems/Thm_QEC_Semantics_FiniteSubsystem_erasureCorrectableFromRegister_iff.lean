-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteSubsystem_erasureCorrectableFromRegister_iff
-- name    : QEC.Semantics.FiniteSubsystem.erasureCorrectableFromRegister_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:43:45.228403+00:00
-- url     : https://prove2.me/theorems/fc7c1bbd-7710-4346-8e44-c1007d617266
-- title:
--   Finite Subsystem: erasure Correctable From Register iff
-- statement:
--   Global-register erasure correctability is definitionally the M2 `Correctable` predicate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Subsystem.lean#L341-L347
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Subsystem.lean#L341-L347

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

theorem QEC.Semantics.FiniteSubsystem.erasureCorrectableFromRegister_iff (S : FiniteSubsystem ι)
    (C : QuantumCode (Qubit.QubitRegister ι))
    (recovery : QuantumChannel S.complementSystem (Qubit.QubitRegister ι)) :
    S.ErasureCorrectableFromRegister C recovery ↔
      Correctable (Qubit.QubitRegister ι) S.complementSystem C
        S.erasureChannelFromRegister recovery := by sorry
