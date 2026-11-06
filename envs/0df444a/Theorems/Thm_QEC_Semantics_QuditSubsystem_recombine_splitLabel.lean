-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_recombine_splitLabel
-- name    : QEC.Semantics.QuditSubsystem.recombine_splitLabel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:45:15.637159+00:00
-- url     : https://prove2.me/theorems/e70a0d39-ce71-4355-8aef-6dd6a5dfd11e
-- title:
--   Qudit Subsystem: recombine split Label
-- statement:
--   Recombining a split label is the inverse of coordinate restriction.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditSubsystem.lean#L245-L247
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditSubsystem.lean#L245-L247

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

theorem QEC.Semantics.QuditSubsystem.recombine_splitLabel (S : QuditSubsystem q) (labels : Qudit.Label q) :
    S.recombineLabel (S.splitLabel labels) = labels := by sorry
