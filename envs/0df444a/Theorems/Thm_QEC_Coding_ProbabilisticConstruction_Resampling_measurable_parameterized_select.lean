-- Prove2me | Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_measurable_parameterized_select
-- name    : QEC.Coding.ProbabilisticConstruction.Resampling.measurable_parameterized_select
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T22:32:40.12332+00:00
-- url     : https://prove2.me/theorems/33ff338c-b91a-42ae-a6d3-07245d4a2af3
-- title:
--   Resampling: measurable parameterized select
-- statement:
--   The Resampling construction uses the measurable parameterized select property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/ParameterizedExecution.lean#L30-L37
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ProbabilisticConstruction/Resampling/ParameterizedExecution.lean#L30-L37

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Termination
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_ParameterizedExecution
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
variable {A W I : Type*} [MeasurableSpace A] [MeasurableSpace W]
variable [Fintype I] [LinearOrder I] [MeasurableSpace I]
variable (B : A → I → Set W) [∀ a i, DecidablePred (· ∈ B a i)]

theorem QEC.Coding.ProbabilisticConstruction.Resampling.measurable_parameterized_select
    (hB : ∀ i, MeasurableSet {z : A × W | z.2 ∈ B z.1 i}) :
    Measurable (fun z : A × W => select (B z.1) z.2) := by sorry
