-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_selected_some_bad
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.selected_some_bad
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:41:47.165811+00:00
-- url     : https://prove2.me/theorems/717f7e37-1455-4a43-a94f-7d2f0caf9017
-- title:
--   Resampling: selected some bad
-- statement:
--   The Resampling construction uses the selected some bad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Execution.lean#L165-L168
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Execution.lean#L165-L168

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

theorem QEC.Coding.ProbabilisticConstruction.Resampling.selected_some_bad (R : Table (X := X)) (n : ℕ) (i : I)
    (h : selected vars bad R n = some i) :
    assignment R (counters vars bad R n) ∈ localEvent vars bad i := by sorry
