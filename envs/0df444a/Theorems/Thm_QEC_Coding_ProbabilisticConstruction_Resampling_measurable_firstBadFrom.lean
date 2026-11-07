-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_measurable_firstBadFrom
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.measurable_firstBadFrom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:18:58.285072+00:00
-- url     : https://prove2.me/theorems/f3b41606-d9b1-45e9-8e44-8afc54d87862
-- title:
--   Resampling: measurable first Bad From
-- statement:
--   The Resampling construction uses the measurable first Bad From property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Execution.lean#L87-L91
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Execution.lean#L87-L91

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_LocalLemma
import Mathlib.Probability.ProductMeasure
import Mathlib.Data.Finset.Sort
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Execution
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
variable {Ω I : Type*} (B : I → Set Ω) [∀ i, DecidablePred (· ∈ B i)]
variable [Fintype I] [LinearOrder I]
variable [MeasurableSpace Ω] [MeasurableSpace I]

theorem QEC.Coding.ProbabilisticConstruction.Resampling.measurable_firstBadFrom (hB : ∀ i, MeasurableSet (B i)) (L : List I) :
    Measurable (firstBadFrom B L) := by sorry
