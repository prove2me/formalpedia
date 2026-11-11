-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_prefixEntry_none_of_above
-- name    : QEC.Coding.BDL26HistoryErrorTelescoping.prefixEntry_none_of_above
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T08:12:21.976356+00:00
-- url     : https://prove2.me/theorems/0f00275c-3597-4669-b521-4664ace5a1dc
-- title:
--   BDL26 History Error Telescoping: prefix Entry none of above
-- statement:
--   The BDL26 History Error Telescoping construction uses the prefix Entry none of above property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping/HistorySums.lean#L202-L207
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping/HistorySums.lean#L202-L207

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

theorem QEC.Coding.BDL26HistoryErrorTelescoping.prefixEntry_none_of_above (D : BDL26DecoderData depth C0 C1 C2)
    (b : LevelIndex depth) (e : CorrectionHistoryEntry D) (h : ¬ e.level ≤ b.val) :
    prefixEntry D b e = none := by sorry
