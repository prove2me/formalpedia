-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_measurable_parameterized_haltTime
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.measurable_parameterized_haltTime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T22:32:56.643584+00:00
-- url     : https://prove2.me/theorems/bcef546a-3fe4-4016-a78b-9e3b5ce67138
-- title:
--   Resampling: measurable parameterized halt Time
-- statement:
--   Nat.find is applied to an everywhere-witnessed total predicate, exactly as in haltTime.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/ParameterizedExecution.lean#L150-L173
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/ParameterizedExecution.lean#L150-L173

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

theorem QEC.Coding.ProbabilisticConstruction.Resampling.measurable_parameterized_haltTime :
    Measurable (fun z : A × Table (X := X) => haltTime vars (bad z.1) z.2) := by sorry
