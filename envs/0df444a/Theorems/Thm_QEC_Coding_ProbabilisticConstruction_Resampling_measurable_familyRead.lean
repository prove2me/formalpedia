-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_measurable_familyRead
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.measurable_familyRead
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:19:36.789847+00:00
-- url     : https://prove2.me/theorems/d2195068-a5a0-4a3a-94e2-4c1b00476801
-- title:
--   Resampling: measurable family Read
-- statement:
--   The Resampling construction uses the measurable family Read property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/TableProbability.lean#L25-L29
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/TableProbability.lean#L25-L29

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

theorem QEC.Coding.ProbabilisticConstruction.Resampling.measurable_familyRead (coords : A → Finset V) (column : ∀ a, coords a → ℕ) :
    Measurable (familyRead (X := X) coords column) := by sorry
