-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_correctionIntervalSum_self
-- name    : QEC.Coding.BDL26HistoryErrorTelescoping.correctionIntervalSum_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:39:00.801789+00:00
-- url     : https://prove2.me/theorems/aabf59fa-0281-41fb-96cd-a8d40c1d7c4f
-- title:
--   BDL26 History Error Telescoping: correction Interval Sum self
-- statement:
--   The BDL26 History Error Telescoping construction uses the correction Interval Sum self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping/HistorySums.lean#L358-L359
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping/HistorySums.lean#L358-L359

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

theorem QEC.Coding.BDL26HistoryErrorTelescoping.correctionIntervalSum_self (sigma : TopInput S n) (a : LevelIndex n) :
    correctionIntervalSum S n sigma a a = 0 := by sorry
