-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_measurableSet_parameterized_localEvent
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.measurableSet_parameterized_localEvent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T22:32:39.796062+00:00
-- url     : https://prove2.me/theorems/7be49ed2-e006-410b-8524-2e3edc4fe92e
-- title:
--   Resampling: measurable Set parameterized local Event
-- statement:
--   Coordinate restriction preserves the parameter and the actual variable addresses.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/ParameterizedExecution.lean#L83-L89
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/ParameterizedExecution.lean#L83-L89

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Termination
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_ParameterizedExecution
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
variable {A V I : Type*} [MeasurableSpace A]
variable [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]
variable [MeasurableSpace I] [MeasurableSingletonClass I]
variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]
variable (vars : I → Finset V) (bad : A → ∀ i, Set (∀ v : vars i, X v))
variable [∀ a i, DecidablePred (· ∈ bad a i)]
variable (hbad : ∀ i, MeasurableSet
  {z : A × (∀ v : vars i, X v) | z.2 ∈ bad z.1 i})
include hbad

theorem QEC.Coding.ProbabilisticConstruction.Resampling.measurableSet_parameterized_localEvent (i : I) :
    MeasurableSet {z : A × (∀ v, X v) | z.2 ∈ localEvent vars (bad z.1) i} := by sorry
