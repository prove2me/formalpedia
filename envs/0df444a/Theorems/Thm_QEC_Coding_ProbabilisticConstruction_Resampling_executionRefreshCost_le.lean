-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_executionRefreshCost_le
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.executionRefreshCost_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:23:26.190036+00:00
-- url     : https://prove2.me/theorems/3f42978f-3371-4ee1-8ec5-0b182686a6e7
-- title:
--   Resampling: execution Refresh Cost le
-- statement:
--   The Resampling construction uses the execution Refresh Cost le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Cost.lean#L78-L89
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Cost.lean#L78-L89

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Termination
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Cost
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
variable {I V : Type*} [Fintype I] [LinearOrder I] [Fintype V] [DecidableEq V]
variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]
variable (vars : I → Finset V) (bad : ∀ i, Set (∀ v : vars i, X v))
variable [∀ i, DecidablePred (· ∈ bad i)]

theorem QEC.Coding.ProbabilisticConstruction.Resampling.executionRefreshCost_le (sampleCost : V → ℝ≥0∞) (C : ℝ≥0∞)
    (hC : ∀ v, sampleCost v ≤ C) (q : ℕ) (hq : ∀ i, (vars i).card ≤ q)
    (R : Table (X := X)) (n : ℕ) :
    executionRefreshCost vars bad sampleCost R n ≤ (q : ℝ≥0∞) * C := by sorry
