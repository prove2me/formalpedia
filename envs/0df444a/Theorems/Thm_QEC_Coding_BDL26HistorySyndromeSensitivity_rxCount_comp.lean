-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_rxCount_comp
-- name    : QEC.Coding.BDL26HistorySyndromeSensitivity.rxCount_comp
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T09:58:05.051727+00:00
-- url     : https://prove2.me/theorems/7b669309-b4f2-4c8f-bc02-7a8673954378
-- title:
--   BDL26 History Syndrome Sensitivity: rx Count comp
-- statement:
--   The BDL26 History Syndrome Sensitivity construction uses the rx Count comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity/Intervals.lean#L203-L207
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity/Intervals.lean#L203-L207

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

theorem QEC.Coding.BDL26HistorySyndromeSensitivity.rxCount_comp (a b c : Nat) (hab : a ≤ b) (hbc : b ≤ c) :
    rxCount a c = rxCount a b + rxCount b c := by sorry
