-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_propagate_succ
-- name    : QEC.Coding.BDL26HistorySyndromeSensitivity.propagate_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:36:21.061063+00:00
-- url     : https://prove2.me/theorems/965c99dd-2b1b-4245-978e-cd74262d178c
-- title:
--   BDL26 History Syndrome Sensitivity: propagate succ
-- statement:
--   The BDL26 History Syndrome Sensitivity construction uses the propagate succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity/Intervals.lean#L81-L88
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity/Intervals.lean#L81-L88

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Snapshots
import Mathlib.Order.Interval.Finset.Nat
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Intervals
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open MultiscaleDecoder
open scoped Classical
variable (S : OddScale) (n : Nat)

theorem QEC.Coding.BDL26HistorySyndromeSensitivity.propagate_succ (b : Nat) (hb : b+1 ≤ n) (a : LevelIndex n)
    (ha : a.val ≤ b) (A : Finset (Coordinates S n ⟨b+1,Nat.lt_succ_of_le hb⟩)) :
    propagate S n (b+1) hb a (by omega) A =
      propagate S n b (by omega) a ha
        (stepPropagation S (n+2) (LevelTwoHistory.physicalStep ⟨b,by omega⟩) A) := by sorry
