-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_totalSteps_eq_haltTime
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.totalSteps_eq_haltTime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:27:37.421657+00:00
-- url     : https://prove2.me/theorems/5013042f-f04c-442e-8035-e77c6d7699f6
-- title:
--   Resampling: total Steps eq halt Time
-- statement:
--   The total count equals the number of transitions before the least clean scan.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Termination.lean#L99-L104
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Termination.lean#L99-L104

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Expectation
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Termination
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
variable {I V : Type*} [Fintype I] [LinearOrder I] [Fintype V] [DecidableEq V]
variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]
variable (vars : I → Finset V) (bad : ∀ i, Set (∀ v : vars i, X v))
variable [∀ i, DecidablePred (· ∈ bad i)]

theorem QEC.Coding.ProbabilisticConstruction.Resampling.totalSteps_eq_haltTime (R : Table (X := X)) (h : Halts vars bad R) :
    totalSteps vars bad R = (haltTime vars bad R : ℝ≥0∞) := by sorry
