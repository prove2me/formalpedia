-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_actualHistory_through
-- name    : QEC.Coding.BDL26HistoryErrorTelescoping.actualHistory_through
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:11:41.591868+00:00
-- url     : https://prove2.me/theorems/879f7fde-9ffe-45d2-be77-e51149bd9573
-- title:
--   BDL26 History Error Telescoping: actual History through
-- statement:
--   The BDL26 History Error Telescoping construction uses the actual History through property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping/HistorySums.lean#L380-L391
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping/HistorySums.lean#L380-L391

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

theorem QEC.Coding.BDL26HistoryErrorTelescoping.actualHistory_through (sigma : TopInput S n) (b : LevelIndex n) :
    historyThrough (SuffixData S n) (actualHistory S n sigma) b =
      prefixHistory (SuffixData S n)
        (LevelTwoHistory.suffixSteps _ (actualAboveTwoSteps S n)) (actualBase S n)
        b.val (Nat.le_of_lt_succ b.isLt) (actualInputs S n sigma b) := by sorry
