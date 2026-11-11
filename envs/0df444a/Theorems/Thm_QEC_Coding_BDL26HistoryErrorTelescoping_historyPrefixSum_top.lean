-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_historyPrefixSum_top
-- name    : QEC.Coding.BDL26HistoryErrorTelescoping.historyPrefixSum_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:12:22.04994+00:00
-- url     : https://prove2.me/theorems/b7ff7388-c6cb-478e-a1df-e9602d4697dc
-- title:
--   BDL26 History Error Telescoping: history Prefix Sum top
-- statement:
--   The BDL26 History Error Telescoping construction uses the history Prefix Sum top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping/HistorySums.lean#L164-L179
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping/HistorySums.lean#L164-L179

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

theorem QEC.Coding.BDL26HistoryErrorTelescoping.historyPrefixSum_top (D : BDL26DecoderData depth C0 C1 C2)
    (H : CorrectionHistory D) :
    historyPrefixSum D H (TopIndex depth) = historyLiftedCorrection D H := by sorry
