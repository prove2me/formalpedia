-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_selected_none_good
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.selected_none_good
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:41:50.485849+00:00
-- url     : https://prove2.me/theorems/8a2bfdfc-a42c-4df8-a814-33cf304b8b73
-- title:
--   Resampling: selected none good
-- statement:
--   The Resampling construction uses the selected none good property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Execution.lean#L170-L173
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Execution.lean#L170-L173

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

theorem QEC.Coding.ProbabilisticConstruction.Resampling.selected_none_good (R : Table (X := X)) (n : ℕ)
    (h : selected vars bad R n = none) :
    ∀ i, assignment R (counters vars bad R n) ∉ localEvent vars bad i := by sorry
