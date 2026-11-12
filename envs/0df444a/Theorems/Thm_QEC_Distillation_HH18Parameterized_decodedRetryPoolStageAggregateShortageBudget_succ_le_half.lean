-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolStageAggregateShortageBudget_succ_le_half
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolStageAggregateShortageBudget_succ_le_half
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:24:08.468694+00:00
-- url     : https://prove2.me/theorems/ed3ba91e-c13f-4881-b2c3-3f080d885c04
-- title:
--   HH18 Parameterized: decoded Retry Pool Stage Aggregate Shortage Budget succ le half
-- statement:
--   After paying for twice as many dyadic slots and all new logical branches,
--   the aggregate stage budget still contracts by a factor of two.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Schedule/SuccessBudget.lean#L234-L275
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Schedule/SuccessBudget.lean#L234-L275

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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolStageAggregateShortageBudget_succ_le_half
    {w r m : Nat} (h : Admissible w r m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hpool : decodedRetryPoolInitialPoolingDomain w r m epsilon)
    (stage : Nat) :
    decodedRetryPoolStageAggregateShortageBudget w r m epsilon (stage + 1) <=
      decodedRetryPoolStageAggregateShortageBudget w r m epsilon stage / 2 := by sorry
