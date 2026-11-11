-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_historyIntervalSum_comp
-- name    : QEC.Coding.BDL26HistoryErrorTelescoping.historyIntervalSum_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:13:11.978328+00:00
-- url     : https://prove2.me/theorems/71297859-203b-4722-b741-4c4d16a12173
-- title:
--   BDL26 History Error Telescoping: history Interval Sum comp
-- statement:
--   The BDL26 History Error Telescoping construction uses the history Interval Sum comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping/HistorySums.lean#L151-L162
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping/HistorySums.lean#L151-L162

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

theorem QEC.Coding.BDL26HistoryErrorTelescoping.historyIntervalSum_comp (D : BDL26DecoderData depth C0 C1 C2)
    (H : CorrectionHistory D) (a b c : LevelIndex depth)
    (hab : a.val ≤ b.val) (hbc : b.val ≤ c.val) :
    historyIntervalSum D H a c =
      intervalMap1 D b c hbc (historyIntervalSum D H a b) + historyIntervalSum D H b c := by sorry
