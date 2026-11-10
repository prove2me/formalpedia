-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_measurable_parameterized_assignment
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.measurable_parameterized_assignment
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T22:32:35.926664+00:00
-- url     : https://prove2.me/theorems/fb478b41-2ea5-4258-9612-40f3e0ca2344
-- title:
--   Resampling: measurable parameterized assignment
-- statement:
--   The lookup index is the countable SECOND factor; no separate-section shortcut is used.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/ParameterizedExecution.lean#L92-L99
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/ParameterizedExecution.lean#L92-L99

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

theorem QEC.Coding.ProbabilisticConstruction.Resampling.measurable_parameterized_assignment
    {c : A × Table (X := X) → Counters V} (hc : Measurable c) :
    Measurable (fun z : A × Table (X := X) => assignment z.2 (c z)) := by sorry
