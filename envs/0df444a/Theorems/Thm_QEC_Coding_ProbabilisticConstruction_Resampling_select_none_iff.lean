-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_select_none_iff
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.select_none_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:18:52.202108+00:00
-- url     : https://prove2.me/theorems/911441b5-f9ba-4add-b7b6-7bf87fe43705
-- title:
--   Resampling: select none iff
-- statement:
--   The Resampling construction uses the select none iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Execution.lean#L75-L76
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Execution.lean#L75-L76

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_LocalLemma
import Mathlib.Probability.ProductMeasure
import Mathlib.Data.Finset.Sort
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Execution
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
variable {Ω I : Type*} (B : I → Set Ω) [∀ i, DecidablePred (· ∈ B i)]
variable [Fintype I] [LinearOrder I]

theorem QEC.Coding.ProbabilisticConstruction.Resampling.select_none_iff (ω : Ω) : select B ω = none ↔ ∀ i, ω ∉ B i := by sorry
