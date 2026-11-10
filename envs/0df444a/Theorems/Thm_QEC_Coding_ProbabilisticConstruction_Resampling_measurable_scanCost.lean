-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_measurable_scanCost
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.measurable_scanCost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:29:13.211836+00:00
-- url     : https://prove2.me/theorems/8f642489-2df3-489b-9767-ab7b98682b2f
-- title:
--   Resampling: measurable scan Cost
-- statement:
--   The Resampling construction uses the measurable scan Cost property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Cost.lean#L38-L42
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Cost.lean#L38-L42

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Termination
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Cost
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
variable {Ω I : Type*} (B : I → Set Ω) [∀ i, DecidablePred (· ∈ B i)]

theorem QEC.Coding.ProbabilisticConstruction.Resampling.measurable_scanCost [MeasurableSpace Ω] (hB : ∀ i, MeasurableSet (B i))
    (queryCost : I → ℝ≥0∞) (L : List I) : Measurable (scanCost B queryCost L) := by sorry
