-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_measurable_prefixCount
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.measurable_prefixCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:26:11.791689+00:00
-- url     : https://prove2.me/theorems/f6993481-362d-4c8e-9732-ec459dc3d90a
-- title:
--   Resampling: measurable prefix Count
-- statement:
--   The Resampling construction uses the measurable prefix Count property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Expectation.lean#L31-L38
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Expectation.lean#L31-L38

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_OccurrenceCounting
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Expectation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
variable {I V : Type*} [Fintype I] [LinearOrder I] [Fintype V] [DecidableEq V]
variable [MeasurableSpace I] [MeasurableSingletonClass I]
variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]
variable (vars : I → Finset V) (bad : ∀ i, Set (∀ v : vars i, X v))
variable [∀ i, DecidablePred (· ∈ bad i)]

theorem QEC.Coding.ProbabilisticConstruction.Resampling.measurable_prefixCount (hbad : ∀ i, MeasurableSet (bad i)) (T : ℕ) (i : I) :
    Measurable (fun R : Table (X := X) => (prefixCount vars bad R T i : ℝ≥0∞)) := by sorry
