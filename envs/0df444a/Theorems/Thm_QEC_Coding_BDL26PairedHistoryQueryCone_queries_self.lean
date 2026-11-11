-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedHistoryQueryCone_queries_self
-- name    : QEC.Coding.BDL26PairedHistoryQueryCone.queries_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T11:01:29.071602+00:00
-- url     : https://prove2.me/theorems/0816293f-b38a-4ab3-a2d2-56d0b9644468
-- title:
--   BDL26 Paired History Query Cone: queries self
-- statement:
--   The BDL26 Paired History Query Cone construction uses the queries self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/PairedHistoryQueryCone.lean#L102-L107
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/PairedHistoryQueryCone.lean#L102-L107

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

theorem QEC.Coding.BDL26PairedHistoryQueryCone.queries_self (e : TopWord S n) (a : LevelIndex n) :
    queries S n e a a = querySeed S n e a := by sorry
