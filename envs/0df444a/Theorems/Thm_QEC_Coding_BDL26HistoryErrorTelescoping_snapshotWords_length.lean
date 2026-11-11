-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_snapshotWords_length
-- name    : QEC.Coding.BDL26HistoryErrorTelescoping.snapshotWords_length
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T10:44:24.256708+00:00
-- url     : https://prove2.me/theorems/a9004ebf-d3d9-47a1-9ae5-3c691bef096b
-- title:
--   BDL26 History Error Telescoping: snapshot Words length
-- statement:
--   The BDL26 History Error Telescoping construction uses the snapshot Words length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping/HistorySums.lean#L516-L527
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping/HistorySums.lean#L516-L527

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

theorem QEC.Coding.BDL26HistoryErrorTelescoping.snapshotWords_length (sigma : TopInput S n) (a : LevelIndex n)
    (b : Nat) (hb : b ≤ n) (ha : a.val ≤ b) :
    (snapshotWords S n sigma a b hb ha).length = b-a.val := by sorry
