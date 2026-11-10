-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_measurable_parameterized_step
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.measurable_parameterized_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T22:32:52.95973+00:00
-- url     : https://prove2.me/theorems/6adf45f3-db2f-4915-be18-319c68c7062a
-- title:
--   Resampling: measurable parameterized step
-- statement:
--   The Resampling construction uses the measurable parameterized step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/ParameterizedExecution.lean#L102-L120
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/ParameterizedExecution.lean#L102-L120

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

theorem QEC.Coding.ProbabilisticConstruction.Resampling.measurable_parameterized_step
    {c : A × Table (X := X) → Counters V} (hc : Measurable c) :
    Measurable (fun z : A × Table (X := X) => step vars (bad z.1) z.2 (c z)) := by sorry
