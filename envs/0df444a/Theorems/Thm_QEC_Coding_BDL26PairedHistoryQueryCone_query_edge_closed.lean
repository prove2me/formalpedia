-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedHistoryQueryCone_query_edge_closed
-- name    : QEC.Coding.BDL26PairedHistoryQueryCone.query_edge_closed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T11:09:43.658697+00:00
-- url     : https://prove2.me/theorems/4d328130-6632-4aa7-9254-e12b6b974ae0
-- title:
--   BDL26 Paired History Query Cone: query edge closed
-- statement:
--   The BDL26 Paired History Query Cone construction uses the query edge closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/PairedHistoryQueryCone.lean#L143-L149
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/PairedHistoryQueryCone.lean#L143-L149

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

theorem QEC.Coding.BDL26PairedHistoryQueryCone.query_edge_closed (e : TopWord S n) (a : LevelIndex n) (i : StepIndex n)
    (ha : a.val ≤ i.val) (z : Coordinates S n i.castSucc)
    (hz : z ∈ queries S n e a i.castSucc) (p : Coordinates S n i.succ)
    (hp : p ∈ coarseRead S (n+2) (LevelTwoHistory.physicalStep i) z) :
    p ∈ queries S n e a i.succ := by sorry
