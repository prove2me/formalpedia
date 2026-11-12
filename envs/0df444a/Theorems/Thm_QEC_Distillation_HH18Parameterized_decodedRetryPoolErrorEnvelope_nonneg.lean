-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolErrorEnvelope_nonneg
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolErrorEnvelope_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:43:50.10329+00:00
-- url     : https://prove2.me/theorems/3dda3948-3f2f-4fe5-9d1c-1cdc7a9dfaab
-- title:
--   HH18 Parameterized: decoded Retry Pool Error Envelope nonneg
-- statement:
--   The distance-power envelope is nonnegative at every finite stage.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Schedule/SuccessBudget.lean#L51-L59
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Schedule/SuccessBudget.lean#L51-L59

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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolErrorEnvelope_nonneg (w r m : Nat)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (stage : Nat) :
    0 <= routedDepthErrorEnvelope w r m epsilon stage := by sorry
