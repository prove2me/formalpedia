-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_executionScanCost_le
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.executionScanCost_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:29:36.292878+00:00
-- url     : https://prove2.me/theorems/7944648e-5514-4704-b063-99e58fe2a062
-- title:
--   Resampling: execution Scan Cost le
-- statement:
--   The Resampling construction uses the execution Scan Cost le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Cost.lean#L72-L76
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Cost.lean#L72-L76

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

theorem QEC.Coding.ProbabilisticConstruction.Resampling.executionScanCost_le (queryCost : I → ℝ≥0∞) (C : ℝ≥0∞)
    (hC : ∀ i, queryCost i ≤ C) (R : Table (X := X)) (n : ℕ) :
    executionScanCost vars bad queryCost R n ≤ (Fintype.card I : ℝ≥0∞) * C := by sorry
