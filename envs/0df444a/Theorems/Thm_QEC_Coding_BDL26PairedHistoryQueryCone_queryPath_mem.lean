-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedHistoryQueryCone_queryPath_mem
-- name    : QEC.Coding.BDL26PairedHistoryQueryCone.queryPath_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T11:31:12.777207+00:00
-- url     : https://prove2.me/theorems/bece77e1-0fef-4d4d-ab9d-39876750f896
-- title:
--   BDL26 Paired History Query Cone: query Path mem
-- statement:
--   The BDL26 Paired History Query Cone construction uses the query Path mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/PairedHistoryQueryCone.lean#L163-L169
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/PairedHistoryQueryCone.lean#L163-L169

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

theorem QEC.Coding.BDL26PairedHistoryQueryCone.queryPath_mem (e : TopWord S n) (a : LevelIndex n) {b : LevelIndex n}
    {p : Coordinates S n b} (path : QueryPath S n e a b p) :
    p ∈ queries S n e a b := by sorry
