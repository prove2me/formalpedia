-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_erasureRecoverableFromRegister_mono
-- name    : QEC.Semantics.QuditSubsystem.erasureRecoverableFromRegister_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:21:00.605542+00:00
-- url     : https://prove2.me/theorems/e0c2191f-9efd-4875-affc-add61e4be33d
-- title:
--   Qudit Subsystem: erasure Recoverable From Register mono
-- statement:
--   Recovery after erasing `T` yields recovery after erasing any selected subset
--   `S`: the recovery first receives the explicit CPTP discard of `T \\ S`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditSubsystem.lean#L857-L869
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditSubsystem.lean#L857-L869

import Definitions.Def_QEC_Semantics_Channels_Core
import Mathlib.Analysis.InnerProductSpace.PiL2
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Semantics.QuditSubsystem
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {q : ι → Nat}

theorem QEC.Semantics.QuditSubsystem.erasureRecoverableFromRegister_mono (S T : QuditSubsystem q)
    (hST : S.selected ⊆ T.selected) (C : QuantumCode (Qudit.QuditRegister q)) :
    T.ErasureRecoverableFromRegister C → S.ErasureRecoverableFromRegister C := by sorry
