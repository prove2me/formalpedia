-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_propagate_mono
-- name    : QEC.Coding.BDL26HistorySyndromeSensitivity.propagate_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:51:12.990785+00:00
-- url     : https://prove2.me/theorems/6f428439-549d-4078-ac27-33a5c4944d67
-- title:
--   BDL26 History Syndrome Sensitivity: propagate mono
-- statement:
--   The BDL26 History Syndrome Sensitivity construction uses the propagate mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity/Intervals.lean#L90-L104
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity/Intervals.lean#L90-L104

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

theorem QEC.Coding.BDL26HistorySyndromeSensitivity.propagate_mono (b : Nat) (hb : b ≤ n) (a : LevelIndex n) (ha : a.val ≤ b)
    {A B : Finset (Coordinates S n ⟨b,Nat.lt_succ_of_le hb⟩)} (hab : A ⊆ B) :
    propagate S n b hb a ha A ⊆ propagate S n b hb a ha B := by sorry
