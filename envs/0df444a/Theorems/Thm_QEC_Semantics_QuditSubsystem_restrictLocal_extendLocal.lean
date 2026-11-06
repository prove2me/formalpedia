-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_restrictLocal_extendLocal
-- name    : QEC.Semantics.QuditSubsystem.restrictLocal_extendLocal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:12:31.842735+00:00
-- url     : https://prove2.me/theorems/cac3105c-2b3c-4ce8-a12f-dca630e8ab8a
-- title:
--   Qudit Subsystem: restrict Local extend Local
-- statement:
--   Restriction is a left inverse to identity extension of selected local operators.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditSubsystem.lean#L343-L352
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditSubsystem.lean#L343-L352

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

theorem QEC.Semantics.QuditSubsystem.restrictLocal_extendLocal (S : QuditSubsystem q) (hq : ∀ i, 0 < q i)
    (A : Operator S.selectedSystem) :
    S.restrictLocal hq (S.extendLocal A) = A := by sorry
