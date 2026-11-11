-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_actual_interval_support
-- name    : QEC.Coding.BDL26HistorySyndromeSensitivity.actual_interval_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:51:58.193495+00:00
-- url     : https://prove2.me/theorems/70793f38-d24d-4951-8701-69520d29a030
-- title:
--   BDL26 History Syndrome Sensitivity: actual interval support
-- statement:
--   The BDL26 History Syndrome Sensitivity construction uses the actual interval support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity/Intervals.lean#L209-L216
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity/Intervals.lean#L209-L216

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

theorem QEC.Coding.BDL26HistorySyndromeSensitivity.actual_interval_support (sigma tau : TopInput S n) (a b : LevelIndex n)
    (ha : a.val ≤ b.val) :
    hammingSupport (actualReadout S n sigma a + actualReadout S n tau a) ⊆
      propagate S n b.val (Nat.le_of_lt_succ b.isLt) a ha
        (hammingSupport (actualReadout S n sigma b + actualReadout S n tau b)) := by sorry
