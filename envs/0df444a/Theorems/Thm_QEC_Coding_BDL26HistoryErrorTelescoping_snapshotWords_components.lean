-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_snapshotWords_components
-- name    : QEC.Coding.BDL26HistoryErrorTelescoping.snapshotWords_components
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:14:50.743384+00:00
-- url     : https://prove2.me/theorems/fd8473fe-7909-4986-b622-d5a095b6b6a4
-- title:
--   BDL26 History Error Telescoping: snapshot Words components
-- statement:
--   The BDL26 History Error Telescoping construction uses the snapshot Words components property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping/HistorySums.lean#L529-L531
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping/HistorySums.lean#L529-L531

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_Intervals
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_HistorySums
import Theorems.Thm_QEC_Semantics_QuditSubsystem_ScalarCompression_sum

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistoryErrorTelescoping
open MultiscaleDecoder BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open BDL26DecodingGraph
open scoped Classical
universe u v
variable (S : OddScale) (n : Nat)

theorem QEC.Coding.BDL26HistoryErrorTelescoping.snapshotWords_components (sigma : TopInput S n) (i : StepIndex n) :
    (actualOutput S n sigma i).correction = (actualOutput S n sigma i).localComponents.sum := by sorry
