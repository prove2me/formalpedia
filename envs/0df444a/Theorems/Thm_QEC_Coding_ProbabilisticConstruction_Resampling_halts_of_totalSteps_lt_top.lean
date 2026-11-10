-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_halts_of_totalSteps_lt_top
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.halts_of_totalSteps_lt_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:28:00.96087+00:00
-- url     : https://prove2.me/theorems/8289190c-8f5f-48c7-a95a-07478c0608e8
-- title:
--   Resampling: halts of total Steps lt top
-- statement:
--   An endless active execution would have at least n resamplings for every n.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Termination.lean#L37-L55
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Termination.lean#L37-L55

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

theorem QEC.Coding.ProbabilisticConstruction.Resampling.halts_of_totalSteps_lt_top (R : Table (X := X))
    (hf : totalSteps vars bad R < ∞) : Halts vars bad R := by sorry
