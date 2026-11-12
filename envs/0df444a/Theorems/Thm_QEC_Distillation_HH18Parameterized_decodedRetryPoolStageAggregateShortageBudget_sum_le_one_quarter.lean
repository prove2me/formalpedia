-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolStageAggregateShortageBudget_sum_le_one_quarter
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolStageAggregateShortageBudget_sum_le_one_quarter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:24:08.400335+00:00
-- url     : https://prove2.me/theorems/8d66e05a-9cef-4cc3-bc46-ec758724ab0a
-- title:
--   HH18 Parameterized: decoded Retry Pool Stage Aggregate Shortage Budget sum le one quarter
-- statement:
--   The finite sum of all literal stage/pool shortage budgets is uniformly
--   bounded by one quarter.  This is the numerical union-bound budget later
--   consumed by the actual physical history proof.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Schedule/SuccessBudget.lean#L280-L309
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Schedule/SuccessBudget.lean#L280-L309

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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolStageAggregateShortageBudget_sum_le_one_quarter
    {w r m : Nat} (h : Admissible w r m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hpool : decodedRetryPoolInitialPoolingDomain w r m epsilon)
    (depth : Nat) :
    (∑ stage : Fin depth,
      decodedRetryPoolStageAggregateShortageBudget w r m epsilon stage.1) <= 1 / 4 := by sorry
