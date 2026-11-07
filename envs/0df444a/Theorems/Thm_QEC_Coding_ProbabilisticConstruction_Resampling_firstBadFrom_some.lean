-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_firstBadFrom_some
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.firstBadFrom_some
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:18:49.25702+00:00
-- url     : https://prove2.me/theorems/8dd4833e-2320-407a-a40f-f040e54edd81
-- title:
--   Resampling: first Bad From some
-- statement:
--   The Resampling construction uses the first Bad From some property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Execution.lean#L39-L50
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/Execution.lean#L39-L50

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_LocalLemma
import Mathlib.Probability.ProductMeasure
import Mathlib.Data.Finset.Sort
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Execution
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
variable {Ω I : Type*} (B : I → Set Ω) [∀ i, DecidablePred (· ∈ B i)]

theorem QEC.Coding.ProbabilisticConstruction.Resampling.firstBadFrom_some {L : List I} {ω : Ω} {i : I}
    (h : firstBadFrom B L ω = some i) : i ∈ L ∧ ω ∈ B i := by sorry
