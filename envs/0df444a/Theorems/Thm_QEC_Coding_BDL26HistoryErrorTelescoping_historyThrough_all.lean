-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_historyThrough_all
-- name    : QEC.Coding.BDL26HistoryErrorTelescoping.historyThrough_all
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:12:22.435762+00:00
-- url     : https://prove2.me/theorems/3c795667-7d33-4894-a0e5-f918f2964d86
-- title:
--   BDL26 History Error Telescoping: history Through all
-- statement:
--   The BDL26 History Error Telescoping construction uses the history Through all property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping/HistorySums.lean#L192-L200
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping/HistorySums.lean#L192-L200

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

theorem QEC.Coding.BDL26HistoryErrorTelescoping.historyThrough_all (D : BDL26DecoderData depth C0 C1 C2)
    (H : CorrectionHistory D) (b : LevelIndex depth)
    (h : ∀ e ∈ H, e.level ≤ b.val) : historyThrough D H b = H := by sorry
