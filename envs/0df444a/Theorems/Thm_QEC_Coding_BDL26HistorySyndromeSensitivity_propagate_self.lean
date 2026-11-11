-- Prove2me | Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_propagate_self
-- name    : QEC.Coding.BDL26HistorySyndromeSensitivity.propagate_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:39:35.327338+00:00
-- url     : https://prove2.me/theorems/f9d39484-2922-4eaa-8547-7c671ab5ff4f
-- title:
--   BDL26 History Syndrome Sensitivity: propagate self
-- statement:
--   The BDL26 History Syndrome Sensitivity construction uses the propagate self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity/Intervals.lean#L72-L79
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/HistorySyndromeSensitivity/Intervals.lean#L72-L79

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

theorem QEC.Coding.BDL26HistorySyndromeSensitivity.propagate_self (b : Nat) (hb : b ≤ n)
    (A : Finset (Coordinates S n ⟨b,Nat.lt_succ_of_le hb⟩)) :
    propagate S n b hb ⟨b,Nat.lt_succ_of_le hb⟩ (Nat.le_refl _) A = A := by sorry
