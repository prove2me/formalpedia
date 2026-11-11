-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_snapshotWords_sum
-- name    : QEC.Coding.BDL26HistoryErrorTelescoping.snapshotWords_sum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T10:43:25.232196+00:00
-- url     : https://prove2.me/theorems/08a35caa-fd71-46cb-98d5-4348ff5153b8
-- title:
--   BDL26 History Error Telescoping: snapshot Words sum
-- statement:
--   The BDL26 History Error Telescoping construction uses the snapshot Words sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping/HistorySums.lean#L489-L514
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping/HistorySums.lean#L489-L514

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_Intervals
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_HistorySums
import Theorems.Thm_QEC_Semantics_QuditSubsystem_ScalarCompression_sum

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistoryErrorTelescoping
open MultiscaleDecoder BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open BDL26DecodingGraph
open scoped Classical
universe u v
variable (S : OddScale) (n : Nat)

theorem QEC.Coding.BDL26HistoryErrorTelescoping.snapshotWords_sum (sigma : TopInput S n) (a : LevelIndex n)
    (b : Nat) (hb : b ≤ n) (ha : a.val ≤ b) :
    (snapshotWords S n sigma a b hb ha).sum =
      correctionIntervalSum S n sigma a ⟨b,Nat.lt_succ_of_le hb⟩ := by sorry
