-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedHistoryQueryCone_paired_step_replay
-- name    : QEC.Coding.BDL26PairedHistoryQueryCone.paired_step_replay
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T11:14:57.836211+00:00
-- url     : https://prove2.me/theorems/b448f77a-fd11-4fde-8422-5d3f8bb64f15
-- title:
--   BDL26 Paired History Query Cone: paired step replay
-- statement:
--   The BDL26 Paired History Query Cone construction uses the paired step replay property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/PairedHistoryQueryCone.lean#L257-L273
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/PairedHistoryQueryCone.lean#L257-L273

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

theorem QEC.Coding.BDL26PairedHistoryQueryCone.paired_step_replay (e : TopWord S n) (a : LevelIndex n) (s t : TopInput S n)
    (htop : AgreeOn (queries S n e a (TopIndex n)) s.val t.val)
    (hflip : AgreeOn (queries S n e a (TopIndex n))
      (perturbTop S n s e).val (perturbTop S n t e).val)
    (i : StepIndex n) (ha : a.val ≤ i.val) :
    (actualOutput S n s i).correction + (actualOutput S n (perturbTop S n s e) i).correction =
      (actualOutput S n t i).correction + (actualOutput S n (perturbTop S n t e) i).correction := by sorry
