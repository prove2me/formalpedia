-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedHistoryQueryCone_query_agreement
-- name    : QEC.Coding.BDL26PairedHistoryQueryCone.query_agreement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T11:02:02.510697+00:00
-- url     : https://prove2.me/theorems/04f9a10d-aae8-4fa3-a963-a13e1ed1acfe
-- title:
--   BDL26 Paired History Query Cone: query agreement
-- statement:
--   Top-cylinder agreement replays every query down to the chosen stop.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/PairedHistoryQueryCone.lean#L208-L234
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/PairedHistoryQueryCone.lean#L208-L234

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

theorem QEC.Coding.BDL26PairedHistoryQueryCone.query_agreement (e : TopWord S n) (a : LevelIndex n) (s t : TopInput S n)
    (htop : AgreeOn (queries S n e a (TopIndex n)) s.val t.val)
    (b : LevelIndex n) (hab : a.val ≤ b.val) :
    AgreeOn (queries S n e a b) (actualInputs S n s b).val (actualInputs S n t b).val := by sorry
