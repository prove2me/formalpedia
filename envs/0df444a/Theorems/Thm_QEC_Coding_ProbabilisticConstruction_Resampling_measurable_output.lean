-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_measurable_output
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.measurable_output
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:28:09.274147+00:00
-- url     : https://prove2.me/theorems/ad6b0005-492f-4e69-883c-271c00fe7494
-- title:
--   Resampling: measurable output
-- statement:
--   The Resampling construction uses the measurable output property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Termination.lean#L150-L153
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Termination.lean#L150-L153

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
variable [MeasurableSpace I] [MeasurableSingletonClass I]
variable (ν : ∀ v, Measure (X v)) [∀ v, IsProbabilityMeasure (ν v)]
variable (hbad : ∀ i, MeasurableSet (bad i))
include hbad

theorem QEC.Coding.ProbabilisticConstruction.Resampling.measurable_output : Measurable (output vars bad (X := X)) := by sorry
