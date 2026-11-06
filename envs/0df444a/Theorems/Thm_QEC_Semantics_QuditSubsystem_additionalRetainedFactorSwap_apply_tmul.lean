-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_additionalRetainedFactorSwap_apply_tmul
-- name    : QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:06:14.142937+00:00
-- url     : https://prove2.me/theorems/a9330b4e-cd28-495c-bc02-f56ce4b3c37a
-- title:
--   Qudit Subsystem: additional Retained Factor Swap apply tmul
-- statement:
--   The additional-retained swap exchanges pure tensor vectors.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditSubsystem.lean#L714-L718
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditSubsystem.lean#L714-L718

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

theorem QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul (S T : QuditSubsystem q)
    (additional : S.additionalRetainedSystem T) (complement : T.complementSystem) :
    S.additionalRetainedFactorSwap T (additional ⊗ₜ[Complex] complement) =
      complement ⊗ₜ[Complex] additional := by sorry

attribute [defeq] QEC.Semantics.QuditSubsystem.additionalRetainedFactorSwap_apply_tmul
