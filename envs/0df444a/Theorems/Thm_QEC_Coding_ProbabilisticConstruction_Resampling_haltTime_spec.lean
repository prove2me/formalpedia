-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_haltTime_spec
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.haltTime_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:27:25.710581+00:00
-- url     : https://prove2.me/theorems/90c55403-bee0-474b-94a9-3da1d2d87ed9
-- title:
--   Resampling: halt Time spec
-- statement:
--   The Resampling construction uses the halt Time spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Termination.lean#L62-L65
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Termination.lean#L62-L65

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

theorem QEC.Coding.ProbabilisticConstruction.Resampling.haltTime_spec (R : Table (X := X)) (h : Halts vars bad R) :
    selected vars bad R (haltTime vars bad R) = none := by sorry
