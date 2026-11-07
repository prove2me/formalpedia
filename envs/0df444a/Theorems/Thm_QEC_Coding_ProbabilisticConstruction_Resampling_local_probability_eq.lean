-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_local_probability_eq
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.local_probability_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:42:31.865193+00:00
-- url     : https://prove2.me/theorems/2dd6fc61-7529-4775-b28d-e0df7f79369e
-- title:
--   Resampling: local probability eq
-- statement:
--   The Resampling construction uses the local probability eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/TableProbability.lean#L74-L77
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/TableProbability.lean#L74-L77

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Execution
import Mathlib.Probability.Independence.InfinitePi
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_TableProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {V A : Type*} [Fintype V] [DecidableEq V] [Fintype A]
variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]
variable (ν : ∀ v, Measure (X v)) [∀ v, IsProbabilityMeasure (ν v)]

theorem QEC.Coding.ProbabilisticConstruction.Resampling.local_probability_eq (S : Finset V) (bad : Set (∀ v : S, X v))
    (hbad : MeasurableSet bad) :
    (Measure.pi ν) (S.restrict ⁻¹' bad) = (Measure.pi (fun v : S => ν v)) bad := by sorry
