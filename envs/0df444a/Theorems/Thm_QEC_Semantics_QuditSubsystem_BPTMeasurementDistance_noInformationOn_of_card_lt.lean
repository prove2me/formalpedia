-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_BPTMeasurementDistance_noInformationOn_of_card_lt
-- name    : QEC.Semantics.QuditSubsystem.BPTMeasurementDistance.noInformationOn_of_card_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:31:25.812885+00:00
-- url     : https://prove2.me/theorems/8f93cffa-75f3-4b1c-9246-d6923664879d
-- title:
--   BPTMeasurement Distance: no Information On of card lt
-- statement:
--   The direct strict-cardinality consequence of the BPT measurement-distance predicate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L1380-L1385
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L1380-L1385

import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
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

theorem QEC.Semantics.QuditSubsystem.BPTMeasurementDistance.noInformationOn_of_card_lt
    {C : QuantumCode (Qudit.QuditRegister q)} {d : Nat}
    (hDistance : BPTMeasurementDistance C d) (S : QuditSubsystem q)
    (hcard : Fintype.card S.SelectedCoordinates < d) :
    NoInformationOn C S := by sorry
