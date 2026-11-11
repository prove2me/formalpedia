-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_intervalEntry_split
-- name    : QEC.Coding.BDL26HistoryErrorTelescoping.intervalEntry_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:11:35.316196+00:00
-- url     : https://prove2.me/theorems/8a7d8d33-6292-4fb5-b8c9-0d27dce9a353
-- title:
--   BDL26 History Error Telescoping: interval Entry split
-- statement:
--   The BDL26 History Error Telescoping construction uses the interval Entry split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping/HistorySums.lean#L116-L149
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping/HistorySums.lean#L116-L149

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

theorem QEC.Coding.BDL26HistoryErrorTelescoping.intervalEntry_split (D : BDL26DecoderData depth C0 C1 C2)
    (a b c : LevelIndex depth) (hab : a.val ≤ b.val) (hbc : b.val ≤ c.val)
    (e : CorrectionHistoryEntry D) :
    (intervalEntry D a c e).getD 0 =
      intervalMap1 D b c hbc ((intervalEntry D a b e).getD 0) +
        (intervalEntry D b c e).getD 0 := by sorry
