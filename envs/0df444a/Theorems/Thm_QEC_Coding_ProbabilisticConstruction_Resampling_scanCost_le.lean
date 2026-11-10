-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_scanCost_le
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.scanCost_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T19:29:02.168702+00:00
-- url     : https://prove2.me/theorems/2991d850-3215-468c-b798-1bb477ab027a
-- title:
--   Resampling: scan Cost le
-- statement:
--   The Resampling construction uses the scan Cost le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Cost.lean#L26-L36
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Cost.lean#L26-L36

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Termination
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Cost
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
variable {Ω I : Type*} (B : I → Set Ω) [∀ i, DecidablePred (· ∈ B i)]

theorem QEC.Coding.ProbabilisticConstruction.Resampling.scanCost_le (queryCost : I → ℝ≥0∞) (C : ℝ≥0∞)
    (hC : ∀ i, queryCost i ≤ C) (L : List I) (ω : Ω) :
    scanCost B queryCost L ω ≤ (L.length : ℝ≥0∞) * C := by sorry
