-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_finiteMeasurementDistance_fails_succ
-- name    : QEC.Semantics.QuditSubsystem.finiteMeasurementDistance_fails_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:55:04.189873+00:00
-- url     : https://prove2.me/theorems/62ab699d-5b10-4969-bd49-ede3fade9227
-- title:
--   Qudit Subsystem: finite Measurement Distance fails succ
-- statement:
--   The Qudit Subsystem construction uses the finite Measurement Distance fails succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/FiniteMeasurementDistance.lean#L107-L110
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/FiniteMeasurementDistance.lean#L107-L110

import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
import Definitions.Def_QEC_Semantics_ErrorCorrection_FiniteMeasurementDistance
set_option autoImplicit false
noncomputable section
open QEC QEC.Semantics QEC.Semantics.QuditSubsystem
open scoped BigOperators
universe u
variable {J : Type u} [Fintype J] [DecidableEq J] (q : J → Nat)

theorem QEC.Semantics.QuditSubsystem.finiteMeasurementDistance_fails_succ (C : QuantumCode (Qudit.QuditRegister q))
    (hfull : ¬ NoInformationOn C (fullRegion q)) :
    ¬ BPTMeasurementDistance C (finiteMeasurementDistance q C + 1) := by sorry
