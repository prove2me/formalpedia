-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_prefixCount_eq_indicator_sum
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.prefixCount_eq_indicator_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:26:57.282791+00:00
-- url     : https://prove2.me/theorems/480397bc-d253-4a91-94db-c535a1f65a79
-- title:
--   Resampling: prefix Count eq indicator sum
-- statement:
--   The Resampling construction uses the prefix Count eq indicator sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Expectation.lean#L23-L29
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Expectation.lean#L23-L29

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

theorem QEC.Coding.ProbabilisticConstruction.Resampling.prefixCount_eq_indicator_sum (R : Table (X := X)) (T : ℕ) (i : I) :
    (prefixCount vars bad R T i : ℝ≥0∞) =
      ∑ n ∈ Finset.range T, ({R : Table (X := X) | selected vars bad R n = some i}).indicator
        (fun _ => (1 : ℝ≥0∞)) R := by sorry
