-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_extendLocalToRegister_operatorSupportedOn
-- name    : QEC.Semantics.QuditSubsystem.extendLocalToRegister_operatorSupportedOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:20:34.045558+00:00
-- url     : https://prove2.me/theorems/e3d6b1e3-424d-4214-a7f8-d8e16ce56517
-- title:
--   Qudit Subsystem: extend Local To Register operator Supported On
-- statement:
--   Every global explicitly extended selected operator is selected-supported.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditSubsystem.lean#L391-L394
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditSubsystem.lean#L391-L394

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

theorem QEC.Semantics.QuditSubsystem.extendLocalToRegister_operatorSupportedOn (S : QuditSubsystem q)
    (A : Operator S.selectedSystem) :
    S.OperatorSupportedOnRegister (S.extendLocalToRegister A) := by sorry
