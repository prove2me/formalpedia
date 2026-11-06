-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_failedThreshold_nonempty
-- name    : QEC.Semantics.QuditSubsystem.failedThreshold_nonempty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:55:07.849725+00:00
-- url     : https://prove2.me/theorems/7c734715-4523-41fc-a5c1-e9ef44bac04d
-- title:
--   Qudit Subsystem: failed Threshold nonempty
-- statement:
--   The Qudit Subsystem construction uses the failed Threshold nonempty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/FiniteMeasurementDistance.lean#L98-L105
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/FiniteMeasurementDistance.lean#L98-L105

import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
import Definitions.Def_QEC_Semantics_ErrorCorrection_FiniteMeasurementDistance
set_option autoImplicit false
noncomputable section
open QEC QEC.Semantics QEC.Semantics.QuditSubsystem
open scoped BigOperators
universe u
variable {J : Type u} [Fintype J] [DecidableEq J] (q : J → Nat)

theorem QEC.Semantics.QuditSubsystem.failedThreshold_nonempty (C : QuantumCode (Qudit.QuditRegister q))
    (hfull : ¬ NoInformationOn C (fullRegion q)) :
    {d : Nat | ¬ BPTMeasurementDistance C (d + 1)}.Nonempty := by sorry
