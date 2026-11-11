-- Prove2me | Theorems.Thm_QEC_Coding_BDL26PairedHistoryQueryCone_interval_pair_replay
-- name    : QEC.Coding.BDL26PairedHistoryQueryCone.interval_pair_replay
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T11:20:18.547215+00:00
-- url     : https://prove2.me/theorems/9ebf1738-30a2-458c-a4c7-8564401b360a
-- title:
--   BDL26 Paired History Query Cone: interval pair replay
-- statement:
--   Linear lifting of the actual step-pair equality through every retained
--   history position, including zero and repeated component words.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/PairedHistoryQueryCone.lean#L502-L550
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/PairedHistoryQueryCone.lean#L502-L550

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

theorem QEC.Coding.BDL26PairedHistoryQueryCone.interval_pair_replay (s t s' t' : TopInput S n) (a b : LevelIndex n)
    (hab : a.val ≤ b.val)
    (hs : ∀ i : StepIndex n, a.val ≤ i.val → i.succ.val ≤ b.val →
      (actualOutput S n s i).correction + (actualOutput S n t i).correction =
        (actualOutput S n s' i).correction + (actualOutput S n t' i).correction) :
    correctionIntervalSum S n s a b + correctionIntervalSum S n t a b =
      correctionIntervalSum S n s' a b + correctionIntervalSum S n t' a b := by sorry
