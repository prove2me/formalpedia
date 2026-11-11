-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedHistoryQueryCone_queries_step
-- name    : QEC.Coding.BDL26PairedHistoryQueryCone.queries_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T11:01:29.462722+00:00
-- url     : https://prove2.me/theorems/5b2eeaa0-b7ab-48d5-a9da-99154d052b65
-- title:
--   BDL26 Paired History Query Cone: queries step
-- statement:
--   The BDL26 Paired History Query Cone construction uses the queries step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/PairedHistoryQueryCone.lean#L123-L134
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/PairedHistoryQueryCone.lean#L123-L134

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

theorem QEC.Coding.BDL26PairedHistoryQueryCone.queries_step (e : TopWord S n) (a : LevelIndex n) (i : StepIndex n)
    (ha : a.val ≤ i.val) :
    queries S n e a i.succ =
      correctionQueries S (n+2) (LevelTwoHistory.physicalStep i) (potential S n e i.succ) ∪
        liftQueries S (n+2) (LevelTwoHistory.physicalStep i) (queries S n e a i.castSucc) := by sorry
