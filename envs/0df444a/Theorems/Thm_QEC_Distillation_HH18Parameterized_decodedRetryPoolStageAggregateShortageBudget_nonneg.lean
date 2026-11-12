-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolStageAggregateShortageBudget_nonneg
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolStageAggregateShortageBudget_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:23:58.57395+00:00
-- url     : https://prove2.me/theorems/7b550c49-7669-400f-854f-6d1149607377
-- title:
--   HH18 Parameterized: decoded Retry Pool Stage Aggregate Shortage Budget nonneg
-- statement:
--   The HH18 Parameterized construction uses the decoded Retry Pool Stage Aggregate Shortage Budget nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Schedule/SuccessBudget.lean#L195-L204
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Schedule/SuccessBudget.lean#L195-L204

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_DyadicSlack
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathYield
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_SuccessBudget
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding
open Coding.ReedMuller Coding.PuncturedReedMuller
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolStageAggregateShortageBudget_nonneg
    (w r m : Nat) (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (stage : Nat) :
    0 <= decodedRetryPoolStageAggregateShortageBudget w r m epsilon stage := by sorry
