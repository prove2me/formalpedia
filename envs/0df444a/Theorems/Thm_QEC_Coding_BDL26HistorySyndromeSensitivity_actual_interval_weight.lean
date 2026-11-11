-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_actual_interval_weight
-- name    : QEC.Coding.BDL26HistorySyndromeSensitivity.actual_interval_weight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:04:39.651203+00:00
-- url     : https://prove2.me/theorems/65d22016-97ca-4a1d-b030-80b97d30306b
-- title:
--   BDL26 History Syndrome Sensitivity: actual interval weight
-- statement:
--   The BDL26 History Syndrome Sensitivity construction uses the actual interval weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity/Intervals.lean#L218-L227
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity/Intervals.lean#L218-L227

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

theorem QEC.Coding.BDL26HistorySyndromeSensitivity.actual_interval_weight (sigma tau : TopInput S n) (a b : LevelIndex n)
    (ha : a.val ≤ b.val) :
    HammingWeight (actualReadout S n sigma a + actualReadout S n tau a) ≤
      57 ^ ((b.val+1)/2 - (a.val+1)/2) *
        HammingWeight (actualReadout S n sigma b + actualReadout S n tau b) := by sorry
