-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_BPTMeasurementDistance_mono
-- name    : QEC.Semantics.QuditSubsystem.BPTMeasurementDistance.mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:55:11.482739+00:00
-- url     : https://prove2.me/theorems/06403da6-414f-4e8b-af5b-1147bf9e33e5
-- title:
--   BPTMeasurement Distance: mono
-- statement:
--   The BPTMeasurement Distance construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/FiniteMeasurementDistance.lean#L78-L82
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/FiniteMeasurementDistance.lean#L78-L82

import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
import Definitions.Def_QEC_Semantics_ErrorCorrection_FiniteMeasurementDistance
set_option autoImplicit false
noncomputable section
open QEC QEC.Semantics QEC.Semantics.QuditSubsystem
open scoped BigOperators
universe u
variable {J : Type u} [Fintype J] [DecidableEq J] (q : J → Nat)

theorem QEC.Semantics.QuditSubsystem.BPTMeasurementDistance.mono {C : QuantumCode (Qudit.QuditRegister q)}
    {d e : Nat} (hd : BPTMeasurementDistance C d) (he : e ≤ d) :
    BPTMeasurementDistance C e := by sorry
