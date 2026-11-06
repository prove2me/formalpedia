-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_restrictLocalFromRegister_extendLocalToRegister
-- name    : QEC.Semantics.QuditSubsystem.restrictLocalFromRegister_extendLocalToRegister
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:48:21.360366+00:00
-- url     : https://prove2.me/theorems/838fc18c-83f5-430f-bef7-536e7d324003
-- title:
--   Qudit Subsystem: restrict Local From Register extend Local To Register
-- statement:
--   Global-register restriction is a left inverse to global local extension.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditSubsystem.lean#L355-L360
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditSubsystem.lean#L355-L360

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

theorem QEC.Semantics.QuditSubsystem.restrictLocalFromRegister_extendLocalToRegister (S : QuditSubsystem q)
    (hq : ∀ i, 0 < q i) (A : Operator S.selectedSystem) :
    S.restrictLocalFromRegister hq (S.extendLocalToRegister A) = A := by sorry
