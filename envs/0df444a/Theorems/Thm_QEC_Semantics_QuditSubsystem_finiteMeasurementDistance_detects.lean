-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_finiteMeasurementDistance_detects
-- name    : QEC.Semantics.QuditSubsystem.finiteMeasurementDistance_detects
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:32:31.189191+00:00
-- url     : https://prove2.me/theorems/77753c75-b5cf-4768-a40a-45805d1094f9
-- title:
--   Qudit Subsystem: finite Measurement Distance detects
-- statement:
--   The Qudit Subsystem construction uses the finite Measurement Distance detects property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/FiniteMeasurementDistance.lean#L89-L96
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/FiniteMeasurementDistance.lean#L89-L96

import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
import Definitions.Def_QEC_Semantics_ErrorCorrection_FiniteMeasurementDistance
set_option autoImplicit false
noncomputable section
open QEC QEC.Semantics QEC.Semantics.QuditSubsystem
open scoped BigOperators
universe u
variable {J : Type u} [Fintype J] [DecidableEq J] (q : J → Nat)

theorem QEC.Semantics.QuditSubsystem.finiteMeasurementDistance_detects (C : QuantumCode (Qudit.QuditRegister q)) :
    BPTMeasurementDistance C (finiteMeasurementDistance q C) := by sorry
