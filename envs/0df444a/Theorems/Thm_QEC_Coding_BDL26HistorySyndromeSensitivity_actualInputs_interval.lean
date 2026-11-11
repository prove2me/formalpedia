-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_actualInputs_interval
-- name    : QEC.Coding.BDL26HistorySyndromeSensitivity.actualInputs_interval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:45:28.081201+00:00
-- url     : https://prove2.me/theorems/cf779c9c-7f51-4bda-9638-088dc5eb32e8
-- title:
--   BDL26 History Syndrome Sensitivity: actual Inputs interval
-- statement:
--   The BDL26 History Syndrome Sensitivity construction uses the actual Inputs interval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity/Intervals.lean#L171-L178
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity/Intervals.lean#L171-L178

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

theorem QEC.Coding.BDL26HistorySyndromeSensitivity.actualInputs_interval (sigma : TopInput S n) (b a : LevelIndex n)
    (ha : a.val ≤ b.val) :
    actualInputs S n sigma a =
      prefixInput (SuffixData S n) (LevelTwoHistory.suffixSteps _ (actualAboveTwoSteps S n))
        b.val (Nat.le_of_lt_succ b.isLt) (actualInputs S n sigma b) a ha := by sorry
