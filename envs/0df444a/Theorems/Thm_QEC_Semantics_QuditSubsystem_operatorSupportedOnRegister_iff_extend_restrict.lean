-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_operatorSupportedOnRegister_iff_extend_restrict
-- name    : QEC.Semantics.QuditSubsystem.operatorSupportedOnRegister_iff_extend_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:46:17.417534+00:00
-- url     : https://prove2.me/theorems/5cf60a37-990c-4339-ac0c-c5df95661cf1
-- title:
--   Qudit Subsystem: operator Supported On Register iff extend restrict
-- statement:
--   Restriction reconstructs exactly the selected-supported global operators.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditSubsystem.lean#L407-L415
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditSubsystem.lean#L407-L415

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

theorem QEC.Semantics.QuditSubsystem.operatorSupportedOnRegister_iff_extend_restrict (S : QuditSubsystem q)
    (hq : ∀ i, 0 < q i) (A : Operator (Qudit.QuditRegister q)) :
    S.OperatorSupportedOnRegister A ↔
      S.extendLocalToRegister (S.restrictLocalFromRegister hq A) = A := by sorry
