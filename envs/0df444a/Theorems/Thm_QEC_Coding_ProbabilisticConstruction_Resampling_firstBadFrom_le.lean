-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_firstBadFrom_le
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.firstBadFrom_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:18:52.969404+00:00
-- url     : https://prove2.me/theorems/c5994c6a-d0a5-412a-b198-2f85b382ec73
-- title:
--   Resampling: first Bad From le
-- statement:
--   The Resampling construction uses the first Bad From le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Execution.lean#L52-L68
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Execution.lean#L52-L68

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_LocalLemma
import Mathlib.Probability.ProductMeasure
import Mathlib.Data.Finset.Sort
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Execution
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
variable {Ω I : Type*} (B : I → Set Ω) [∀ i, DecidablePred (· ∈ B i)]

theorem QEC.Coding.ProbabilisticConstruction.Resampling.firstBadFrom_le [LinearOrder I] {L : List I} (hL : L.Pairwise (· ≤ ·))
    {ω : Ω} {i : I} (hi : firstBadFrom B L ω = some i)
    {j : I} (hj : j ∈ L) (hbad : ω ∈ B j) : i ≤ j := by sorry
