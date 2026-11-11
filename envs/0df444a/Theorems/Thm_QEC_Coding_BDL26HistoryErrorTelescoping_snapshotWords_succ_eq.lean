-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_snapshotWords_succ_eq
-- name    : QEC.Coding.BDL26HistoryErrorTelescoping.snapshotWords_succ_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:11:44.492707+00:00
-- url     : https://prove2.me/theorems/0ac0019f-1886-4941-a9fa-32ffe883e82a
-- title:
--   BDL26 History Error Telescoping: snapshot Words succ eq
-- statement:
--   The BDL26 History Error Telescoping construction uses the snapshot Words succ eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping/HistorySums.lean#L472-L480
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistoryErrorTelescoping/HistorySums.lean#L472-L480

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_Intervals
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_HistorySums
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistoryErrorTelescoping
open MultiscaleDecoder BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open BDL26DecodingGraph
open scoped Classical
universe u v
variable (S : OddScale) (n : Nat)

theorem QEC.Coding.BDL26HistoryErrorTelescoping.snapshotWords_succ_eq (sigma : TopInput S n) (a : LevelIndex n)
    (b : Nat) (hb : b+1 ≤ n) (ha : a.val ≤ b+1) :
    snapshotWords S n sigma a (b+1) hb ha =
      if h : a.val = b+1 then [] else
        let i : StepIndex n := ⟨b,Nat.lt_of_lt_of_le (Nat.lt_succ_self b) hb⟩
        (actualOutput S n sigma i).correction ::
          (snapshotWords S n sigma a b (by omega) (by omega)).map
            ((SuffixData S n).selectedMap i).map1 := by sorry
