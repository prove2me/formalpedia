-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_fullRegion_extension_surjective
-- name    : QEC.Semantics.QuditSubsystem.fullRegion_extension_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:55:27.584757+00:00
-- url     : https://prove2.me/theorems/0120ecdf-d323-41a2-887c-443c6b8d24e7
-- title:
--   Qudit Subsystem: full Region extension surjective
-- statement:
--   On the full region every ambient operator is an actual local extension.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/FiniteMeasurementDistance.lean#L38-L52
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/FiniteMeasurementDistance.lean#L38-L52

import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
import Definitions.Def_QEC_Semantics_ErrorCorrection_FiniteMeasurementDistance
set_option autoImplicit false
noncomputable section
open QEC QEC.Semantics QEC.Semantics.QuditSubsystem
open scoped BigOperators
universe u
variable {J : Type u} [Fintype J] [DecidableEq J] (q : J → Nat)

theorem QEC.Semantics.QuditSubsystem.fullRegion_extension_surjective (hq : ∀ j, 0 < q j) :
    Function.Surjective (fullRegion q).extendLocalToRegister := by sorry
