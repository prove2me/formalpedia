-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_propagate_card
-- name    : QEC.Coding.BDL26HistorySyndromeSensitivity.propagate_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:02:36.271124+00:00
-- url     : https://prove2.me/theorems/029ae26b-08c7-457a-9f68-861c327b4bba
-- title:
--   BDL26 History Syndrome Sensitivity: propagate card
-- statement:
--   The BDL26 History Syndrome Sensitivity construction uses the propagate card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity/Intervals.lean#L113-L137
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity/Intervals.lean#L113-L137

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

theorem QEC.Coding.BDL26HistorySyndromeSensitivity.propagate_card (b : Nat) (hb : b ≤ n) (a : LevelIndex n) (ha : a.val ≤ b)
    (A : Finset (Coordinates S n ⟨b,Nat.lt_succ_of_le hb⟩)) :
    (propagate S n b hb a ha A).card ≤ 57 ^ rxCount a.val b * A.card := by sorry
