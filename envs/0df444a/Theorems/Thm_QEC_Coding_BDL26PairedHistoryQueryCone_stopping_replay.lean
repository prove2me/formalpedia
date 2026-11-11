-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedHistoryQueryCone_stopping_replay
-- name    : QEC.Coding.BDL26PairedHistoryQueryCone.stopping_replay
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T11:14:00.899338+00:00
-- url     : https://prove2.me/theorems/5e7eeb40-c219-481c-9162-9c5bc9fdf1f2
-- title:
--   BDL26 Paired History Query Cone: stopping replay
-- statement:
--   The BDL26 Paired History Query Cone construction uses the stopping replay property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/PairedHistoryQueryCone.lean#L236-L255
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/PairedHistoryQueryCone.lean#L236-L255

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

theorem QEC.Coding.BDL26PairedHistoryQueryCone.stopping_replay (e : TopWord S n) (a : LevelIndex n) (ha : 0 < a.val)
    (s t : TopInput S n)
    (hs : actualInputs S n s a = actualInputs S n (perturbTop S n s e) a)
    (htop : AgreeOn (queries S n e a (TopIndex n)) s.val t.val)
    (hflip : AgreeOn (queries S n e a (TopIndex n))
      (perturbTop S n s e).val (perturbTop S n t e).val) :
    actualInputs S n t a = actualInputs S n (perturbTop S n t e) a := by sorry
