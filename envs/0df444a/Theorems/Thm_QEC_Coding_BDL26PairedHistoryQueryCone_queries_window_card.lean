-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedHistoryQueryCone_queries_window_card
-- name    : QEC.Coding.BDL26PairedHistoryQueryCone.queries_window_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T11:17:44.244509+00:00
-- url     : https://prove2.me/theorems/44093537-c25b-4b98-88d2-90c6ecc8bb49
-- title:
--   BDL26 Paired History Query Cone: queries window card
-- statement:
--   The BDL26 Paired History Query Cone construction uses the queries window card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/PairedHistoryQueryCone.lean#L378-L421
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/PairedHistoryQueryCone.lean#L378-L421

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone_ReadBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_HistorySums
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26PairedHistoryQueryCone
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping MultiscaleDecoder
open scoped Classical BigOperators
variable (S : OddScale) (n : Nat)

theorem QEC.Coding.BDL26PairedHistoryQueryCone.queries_window_card (e : TopWord S n) (a : LevelIndex n) (ha : 0 < a.val)
    (L w : Nat) (hw : HammingWeight ((SuffixData S n).family.coboundary1 (TopIndex n) e) ≤ w)
    (hlen : n-a.val ≤ L) :
    (queries S n e a (TopIndex n)).card ≤ windowBudget S L w := by sorry
