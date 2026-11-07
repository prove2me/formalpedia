-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_measurable_select
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.measurable_select
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:09:33.984314+00:00
-- url     : https://prove2.me/theorems/f1e0c666-4c47-4a40-8d53-080716514d7c
-- title:
--   Resampling: measurable select
-- statement:
--   The Resampling construction uses the measurable select property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Execution.lean#L93-L94
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Execution.lean#L93-L94

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

theorem QEC.Coding.ProbabilisticConstruction.Resampling.measurable_select (hB : ∀ i, MeasurableSet (B i)) : Measurable (select B) := by sorry
