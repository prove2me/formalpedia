-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_rxCount_formula
-- name    : QEC.Coding.BDL26HistorySyndromeSensitivity.rxCount_formula
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:45:09.697203+00:00
-- url     : https://prove2.me/theorems/5d0c3c52-c093-44f1-9747-7063d9fe594e
-- title:
--   BDL26 History Syndrome Sensitivity: rx Count formula
-- statement:
--   The BDL26 History Syndrome Sensitivity construction uses the rx Count formula property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity/Intervals.lean#L42-L53
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity/Intervals.lean#L42-L53

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

theorem QEC.Coding.BDL26HistorySyndromeSensitivity.rxCount_formula (a b : Nat) (hab : a ≤ b) :
    rxCount a b = (b+1)/2 - (a+1)/2 := by sorry
