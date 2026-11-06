-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_extendLocalToRegister_injective
-- name    : QEC.Semantics.QuditSubsystem.extendLocalToRegister_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:20:13.907821+00:00
-- url     : https://prove2.me/theorems/f75614c4-e288-432b-9716-6fa77472c8ba
-- title:
--   Qudit Subsystem: extend Local To Register injective
-- statement:
--   Global local extension is injective.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditSubsystem.lean#L370-L374
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditSubsystem.lean#L370-L374

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

theorem QEC.Semantics.QuditSubsystem.extendLocalToRegister_injective (S : QuditSubsystem q) (hq : ∀ i, 0 < q i) :
    Function.Injective S.extendLocalToRegister := by sorry
