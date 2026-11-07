-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_unselected_assignment_unchanged
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.unselected_assignment_unchanged
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:41:55.971652+00:00
-- url     : https://prove2.me/theorems/fa82f4ac-7c5f-4fa8-b649-f5087a23ba50
-- title:
--   Resampling: unselected assignment unchanged
-- statement:
--   The Resampling construction uses the unselected assignment unchanged property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Execution.lean#L196-L203
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Execution.lean#L196-L203

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_LocalLemma
import Mathlib.Probability.ProductMeasure
import Mathlib.Data.Finset.Sort
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Execution
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]
variable {X : V → Type*}
variable (vars : I → Finset V) (bad : ∀ i, Set (∀ v : vars i, X v))
variable [∀ i, DecidablePred (· ∈ bad i)]

theorem QEC.Coding.ProbabilisticConstruction.Resampling.unselected_assignment_unchanged (R : Table (X := X)) (n : ℕ) (i : I)
    (h : selected vars bad R n = some i) {v : V} (hv : v ∉ vars i) :
    assignment R (counters vars bad R (n + 1)) v =
      assignment R (counters vars bad R n) v := by sorry
