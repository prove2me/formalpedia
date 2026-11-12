-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolErrorEnvelope_succ_le_div_four_mul_logicalOutputCount
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolErrorEnvelope_succ_le_div_four_mul_logicalOutputCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:23:29.387629+00:00
-- url     : https://prove2.me/theorems/f167f240-255c-4954-99f2-66cb0397c440
-- title:
--   HH18 Parameterized: decoded Retry Pool Error Envelope succ le div four mul logical Output Count
-- statement:
--   In the pooling domain the envelope contracts fast enough to pay for four
--   times the number of logical branches at every successor stage.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Schedule/SuccessBudget.lean#L99-L182
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Schedule/SuccessBudget.lean#L99-L182

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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolErrorEnvelope_succ_le_div_four_mul_logicalOutputCount
    {w r m : Nat} (h : Admissible w r m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hpool : decodedRetryPoolInitialPoolingDomain w r m epsilon)
    (stage : Nat) :
    routedDepthErrorEnvelope w r m epsilon (stage + 1) <=
      routedDepthErrorEnvelope w r m epsilon stage /
        (4 * (logicalOutputCount m w : Real)) := by sorry
