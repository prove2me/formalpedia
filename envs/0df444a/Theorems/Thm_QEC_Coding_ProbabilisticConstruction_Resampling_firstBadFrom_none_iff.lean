-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_firstBadFrom_none_iff
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.firstBadFrom_none_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:18:48.4914+00:00
-- url     : https://prove2.me/theorems/72eded9c-aaef-4744-82ac-4e59cbe2de66
-- title:
--   Resampling: first Bad From none iff
-- statement:
--   The Resampling construction uses the first Bad From none iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Execution.lean#L32-L37
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Execution.lean#L32-L37

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_LocalLemma
import Mathlib.Probability.ProductMeasure
import Mathlib.Data.Finset.Sort
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Execution
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
variable {Ω I : Type*} (B : I → Set Ω) [∀ i, DecidablePred (· ∈ B i)]

theorem QEC.Coding.ProbabilisticConstruction.Resampling.firstBadFrom_none_iff (L : List I) (ω : Ω) :
    firstBadFrom B L ω = none ↔ ∀ i ∈ L, ω ∉ B i := by sorry
