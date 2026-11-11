-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedHistoryQueryCone_le_stoppingLevel
-- name    : QEC.Coding.BDL26PairedHistoryQueryCone.le_stoppingLevel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T11:16:57.251359+00:00
-- url     : https://prove2.me/theorems/58e4d514-d587-43ef-9fc3-754ade81298b
-- title:
--   BDL26 Paired History Query Cone: le stopping Level
-- statement:
--   The BDL26 Paired History Query Cone construction uses the le stopping Level property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/PairedHistoryQueryCone.lean#L295-L300
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/PairedHistoryQueryCone.lean#L295-L300

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

theorem QEC.Coding.BDL26PairedHistoryQueryCone.le_stoppingLevel (s : TopInput S n) (e : TopWord S n) (a : LevelIndex n)
    (ha : actualInputs S n s a = actualInputs S n (perturbTop S n s e) a) :
    a ≤ stoppingLevel S n s e := by sorry
