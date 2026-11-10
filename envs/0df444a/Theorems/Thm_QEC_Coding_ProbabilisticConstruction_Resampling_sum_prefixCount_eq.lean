-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_sum_prefixCount_eq
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.sum_prefixCount_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:27:20.563525+00:00
-- url     : https://prove2.me/theorems/8e5aa2e4-27c1-465c-8d1b-ec4a3086daa7
-- title:
--   Resampling: sum prefix Count eq
-- statement:
--   The Resampling construction uses the sum prefix Count eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Termination.lean#L22-L31
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Termination.lean#L22-L31

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

theorem QEC.Coding.ProbabilisticConstruction.Resampling.sum_prefixCount_eq (R : Table (X := X)) (T : ℕ)
    (hactive : ∀ n < T, ∃ i, selected vars bad R n = some i) :
    ∑ i, prefixCount vars bad R T i = T := by sorry
