-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_historyIntervalSum_self
-- name    : QEC.Coding.BDL26HistoryErrorTelescoping.historyIntervalSum_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:10:13.483204+00:00
-- url     : https://prove2.me/theorems/5b601bfc-91bf-4348-96b4-7c2e27e8f514
-- title:
--   BDL26 History Error Telescoping: history Interval Sum self
-- statement:
--   The BDL26 History Error Telescoping construction uses the history Interval Sum self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping/HistorySums.lean#L100-L114
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping/HistorySums.lean#L100-L114

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
variable {depth : Nat} {C0 C1 C2 : LevelIndex depth → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]

theorem QEC.Coding.BDL26HistoryErrorTelescoping.historyIntervalSum_self (D : BDL26DecoderData depth C0 C1 C2)
    (H : CorrectionHistory D) (a : LevelIndex depth) : historyIntervalSum D H a a = 0 := by sorry
