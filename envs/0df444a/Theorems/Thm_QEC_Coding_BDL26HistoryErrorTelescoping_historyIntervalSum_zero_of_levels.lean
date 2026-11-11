-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_historyIntervalSum_zero_of_levels
-- name    : QEC.Coding.BDL26HistoryErrorTelescoping.historyIntervalSum_zero_of_levels
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:12:15.246072+00:00
-- url     : https://prove2.me/theorems/a61ba6b0-837f-4d2d-ba9e-5e93c3da21b6
-- title:
--   BDL26 History Error Telescoping: history Interval Sum zero of levels
-- statement:
--   The BDL26 History Error Telescoping construction uses the history Interval Sum zero of levels property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping/HistorySums.lean#L225-L239
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping/HistorySums.lean#L225-L239

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

theorem QEC.Coding.BDL26HistoryErrorTelescoping.historyIntervalSum_zero_of_levels (D : BDL26DecoderData depth C0 C1 C2)
    (H : CorrectionHistory D) (a b : LevelIndex depth)
    (h : ∀ e ∈ H, e.level ≤ a.val) : historyIntervalSum D H a b = 0 := by sorry
