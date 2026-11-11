-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedHistoryQueryCone_queries_card_budget
-- name    : QEC.Coding.BDL26PairedHistoryQueryCone.queries_card_budget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T11:17:36.273202+00:00
-- url     : https://prove2.me/theorems/e07c77f3-5edb-4e9f-9f7f-4ffd11f01f86
-- title:
--   BDL26 Paired History Query Cone: queries card budget
-- statement:
--   The BDL26 Paired History Query Cone construction uses the queries card budget property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/PairedHistoryQueryCone.lean#L327-L372
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/PairedHistoryQueryCone.lean#L327-L372

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

theorem QEC.Coding.BDL26PairedHistoryQueryCone.queries_card_budget (e : TopWord S n) (a b : LevelIndex n) :
    (queries S n e a b).card ≤ budgetPrefix S n e a b.val (Nat.le_of_lt_succ b.isLt) := by sorry
