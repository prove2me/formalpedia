-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_propagate_comp
-- name    : QEC.Coding.BDL26HistorySyndromeSensitivity.propagate_comp
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T09:56:42.037748+00:00
-- url     : https://prove2.me/theorems/3cb86aea-3a19-441b-a7fd-19be678030d9
-- title:
--   BDL26 History Syndrome Sensitivity: propagate comp
-- statement:
--   The BDL26 History Syndrome Sensitivity construction uses the propagate comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity/Intervals.lean#L180-L201
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity/Intervals.lean#L180-L201

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Snapshots
import Mathlib.Order.Interval.Finset.Nat
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Intervals
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open MultiscaleDecoder
open scoped Classical
variable (S : OddScale) (n : Nat)

theorem QEC.Coding.BDL26HistorySyndromeSensitivity.propagate_comp (c : Nat) (hc : c ≤ n)
    (A : Finset (Coordinates S n ⟨c,Nat.lt_succ_of_le hc⟩))
    (b a : LevelIndex n) (hb : b.val ≤ c) (ha : a.val ≤ b.val) :
    propagate S n c hc a (ha.trans hb) A =
      propagate S n b.val (Nat.le_of_lt_succ b.isLt) a ha
        (propagate S n c hc b hb A) := by sorry
