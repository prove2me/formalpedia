-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_erasureRecoverableFromRegister_iff_exists_correctable
-- name    : QEC.Semantics.QuditSubsystem.erasureRecoverableFromRegister_iff_exists_correctable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:46:58.691485+00:00
-- url     : https://prove2.me/theorems/e0285dff-7f02-457b-a3ea-eb0baef08f24
-- title:
--   Qudit Subsystem: erasure Recoverable From Register iff exists correctable
-- statement:
--   Existential global qudit erasure recoverability stays in the CPTP channel vocabulary.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditSubsystem.lean#L845-L851
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditSubsystem.lean#L845-L851

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

theorem QEC.Semantics.QuditSubsystem.erasureRecoverableFromRegister_iff_exists_correctable (S : QuditSubsystem q)
    (C : QuantumCode (Qudit.QuditRegister q)) :
    S.ErasureRecoverableFromRegister C ↔
      ∃ recovery : QuantumChannel S.complementSystem (Qudit.QuditRegister q),
        Correctable (Qudit.QuditRegister q) S.complementSystem C
          S.erasureChannelFromRegister recovery := by sorry
