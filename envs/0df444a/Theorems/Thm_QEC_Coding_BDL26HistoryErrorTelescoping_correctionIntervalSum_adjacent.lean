-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_correctionIntervalSum_adjacent
-- name    : QEC.Coding.BDL26HistoryErrorTelescoping.correctionIntervalSum_adjacent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:15:24.455836+00:00
-- url     : https://prove2.me/theorems/315d8a06-9980-4c24-a27a-3a09b998ac8e
-- title:
--   BDL26 History Error Telescoping: correction Interval Sum adjacent
-- statement:
--   The BDL26 History Error Telescoping construction uses the correction Interval Sum adjacent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping/HistorySums.lean#L438-L442
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping/HistorySums.lean#L438-L442

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_Intervals
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_HistorySums
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistoryErrorTelescoping
open MultiscaleDecoder BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open BDL26DecodingGraph
open scoped Classical
universe u v
variable (S : OddScale) (n : Nat)

theorem QEC.Coding.BDL26HistoryErrorTelescoping.correctionIntervalSum_adjacent (sigma : TopInput S n) (i : StepIndex n) :
    correctionIntervalSum S n sigma i.castSucc i.succ = (actualOutput S n sigma i).correction := by sorry
