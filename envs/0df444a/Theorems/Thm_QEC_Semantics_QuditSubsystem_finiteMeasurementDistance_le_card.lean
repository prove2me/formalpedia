-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_finiteMeasurementDistance_le_card
-- name    : QEC.Semantics.QuditSubsystem.finiteMeasurementDistance_le_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:32:38.171566+00:00
-- url     : https://prove2.me/theorems/faa46a90-a345-4b51-8efc-07d20b11c10d
-- title:
--   Qudit Subsystem: finite Measurement Distance le card
-- statement:
--   The Qudit Subsystem construction uses the finite Measurement Distance le card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/FiniteMeasurementDistance.lean#L112-L119
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/FiniteMeasurementDistance.lean#L112-L119

import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
import Definitions.Def_QEC_Semantics_ErrorCorrection_FiniteMeasurementDistance
set_option autoImplicit false
noncomputable section
open QEC QEC.Semantics QEC.Semantics.QuditSubsystem
open scoped BigOperators
universe u
variable {J : Type u} [Fintype J] [DecidableEq J] (q : J → Nat)

theorem QEC.Semantics.QuditSubsystem.finiteMeasurementDistance_le_card (C : QuantumCode (Qudit.QuditRegister q))
    (hfull : ¬ NoInformationOn C (fullRegion q)) :
    finiteMeasurementDistance q C ≤ Fintype.card J := by sorry
