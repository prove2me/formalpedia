-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_discardAdditionalRetained_erasureChannelFromRegister_apply
-- name    : QEC.Semantics.QuditSubsystem.discardAdditionalRetained_erasureChannelFromRegister_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:21:11.7072+00:00
-- url     : https://prove2.me/theorems/0f16b72c-ef0c-4418-9769-c7e823caca72
-- title:
--   Qudit Subsystem: discard Additional Retained erasure Channel From Register apply
-- statement:
--   Erasing `T` is exactly erasing `S` and then explicitly discarding the retained
--   coordinates in `T \\ S`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditSubsystem.lean#L774-L796
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditSubsystem.lean#L774-L796

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

theorem QEC.Semantics.QuditSubsystem.discardAdditionalRetained_erasureChannelFromRegister_apply
    (S T : QuditSubsystem q) (hST : S.selected ⊆ T.selected)
    (A : Operator (Qudit.QuditRegister q)) :
    S.discardAdditionalRetained T hST (S.erasureChannelFromRegister A) =
      T.erasureChannelFromRegister A := by sorry
