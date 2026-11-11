-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedHistoryQueryCone_correctionQueries_subset
-- name    : QEC.Coding.BDL26PairedHistoryQueryCone.correctionQueries_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T11:05:39.253823+00:00
-- url     : https://prove2.me/theorems/c9dd2e8b-24e6-4e17-ac85-095386927231
-- title:
--   BDL26 Paired History Query Cone: correction Queries subset
-- statement:
--   The BDL26 Paired History Query Cone construction uses the correction Queries subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/PairedHistoryQueryCone.lean#L136-L141
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/PairedHistoryQueryCone.lean#L136-L141

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

theorem QEC.Coding.BDL26PairedHistoryQueryCone.correctionQueries_subset (e : TopWord S n) (a : LevelIndex n) (i : StepIndex n)
    (ha : a.val ≤ i.val) :
    correctionQueries S (n+2) (LevelTwoHistory.physicalStep i) (potential S n e i.succ) ⊆
      queries S n e a i.succ := by sorry
