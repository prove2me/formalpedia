-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_select_le
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.select_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:41:37.471803+00:00
-- url     : https://prove2.me/theorems/8b3d2612-81cd-4ed4-bae8-277fc217636c
-- title:
--   Resampling: select le
-- statement:
--   The Resampling construction uses the select le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Execution.lean#L81-L83
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Execution.lean#L81-L83

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_LocalLemma
import Mathlib.Probability.ProductMeasure
import Mathlib.Data.Finset.Sort
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Execution
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
variable {Ω I : Type*} (B : I → Set Ω) [∀ i, DecidablePred (· ∈ B i)]
variable [Fintype I] [LinearOrder I]

theorem QEC.Coding.ProbabilisticConstruction.Resampling.select_le {ω : Ω} {i j : I} (hi : select B ω = some i)
    (hj : ω ∈ B j) : i ≤ j := by sorry
