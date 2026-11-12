-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolStageAggregateShortageBudget_zero_le_one_sixteenth
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolStageAggregateShortageBudget_zero_le_one_sixteenth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:23:58.800739+00:00
-- url     : https://prove2.me/theorems/ade17559-1e00-47e5-ae54-0cac3e23afe7
-- title:
--   HH18 Parameterized: decoded Retry Pool Stage Aggregate Shortage Budget zero le one sixteenth
-- statement:
--   The initial aggregate shortage budget is at most one sixteenth.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Schedule/SuccessBudget.lean#L207-L230
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Schedule/SuccessBudget.lean#L207-L230

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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolStageAggregateShortageBudget_zero_le_one_sixteenth
    {w r m : Nat} (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hpool : decodedRetryPoolInitialPoolingDomain w r m epsilon) :
    decodedRetryPoolStageAggregateShortageBudget w r m epsilon 0 <= 1 / 16 := by sorry
