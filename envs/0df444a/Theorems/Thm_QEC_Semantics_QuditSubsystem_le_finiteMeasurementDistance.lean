-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_le_finiteMeasurementDistance
-- name    : QEC.Semantics.QuditSubsystem.le_finiteMeasurementDistance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:32:39.800827+00:00
-- url     : https://prove2.me/theorems/153cb177-338d-4a67-bdb9-893b1c1ac3bb
-- title:
--   Qudit Subsystem: le finite Measurement Distance
-- statement:
--   The Qudit Subsystem construction uses the le finite Measurement Distance property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/FiniteMeasurementDistance.lean#L121-L126
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/FiniteMeasurementDistance.lean#L121-L126

import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
import Definitions.Def_QEC_Semantics_ErrorCorrection_FiniteMeasurementDistance
set_option autoImplicit false
noncomputable section
open QEC QEC.Semantics QEC.Semantics.QuditSubsystem
open scoped BigOperators
universe u
variable {J : Type u} [Fintype J] [DecidableEq J] (q : J → Nat)

theorem QEC.Semantics.QuditSubsystem.le_finiteMeasurementDistance (C : QuantumCode (Qudit.QuditRegister q))
    (hfull : ¬ NoInformationOn C (fullRegion q)) {d : Nat}
    (hd : BPTMeasurementDistance C d) : d ≤ finiteMeasurementDistance q C := by sorry
