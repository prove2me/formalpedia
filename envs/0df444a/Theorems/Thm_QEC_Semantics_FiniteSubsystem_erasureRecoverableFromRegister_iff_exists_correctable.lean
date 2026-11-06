-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteSubsystem_erasureRecoverableFromRegister_iff_exists_correctable
-- name    : QEC.Semantics.FiniteSubsystem.erasureRecoverableFromRegister_iff_exists_correctable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:44:04.736263+00:00
-- url     : https://prove2.me/theorems/d27ac298-17f0-454c-8f8a-35f88f45296f
-- title:
--   Finite Subsystem: erasure Recoverable From Register iff exists correctable
-- statement:
--   Global-register erasure recoverability is stated directly with M2 `Correctable`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Subsystem.lean#L376-L382
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Core/Subsystem.lean#L376-L382

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

theorem QEC.Semantics.FiniteSubsystem.erasureRecoverableFromRegister_iff_exists_correctable (S : FiniteSubsystem ι)
    (C : QuantumCode (Qubit.QubitRegister ι)) :
    S.ErasureRecoverableFromRegister C ↔
      ∃ recovery : QuantumChannel S.complementSystem (Qubit.QubitRegister ι),
        Correctable (Qubit.QubitRegister ι) S.complementSystem C
          S.erasureChannelFromRegister recovery := by sorry
