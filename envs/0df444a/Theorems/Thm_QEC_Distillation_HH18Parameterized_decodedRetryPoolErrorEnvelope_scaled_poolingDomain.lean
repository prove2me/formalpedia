-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolErrorEnvelope_scaled_poolingDomain
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolErrorEnvelope_scaled_poolingDomain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:23:32.745666+00:00
-- url     : https://prove2.me/theorems/ff3971b9-8a54-45e7-a2a2-b604b2f6d8c1
-- title:
--   HH18 Parameterized: decoded Retry Pool Error Envelope scaled pooling Domain
-- statement:
--   The strong pooling threshold persists for the exact distance-power
--   envelope, not merely for the actual path rates that it bounds.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Schedule/SuccessBudget.lean#L63-L95
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Schedule/SuccessBudget.lean#L63-L95

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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolErrorEnvelope_scaled_poolingDomain
    {w r m : Nat} (h : Admissible w r m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hpool : decodedRetryPoolInitialPoolingDomain w r m epsilon)
    (stage : Nat) :
    routedDepthIterationScale w r m *
        routedDepthErrorEnvelope w r m epsilon stage <=
      1 / (64 * (logicalOutputCount m w : Real)) := by sorry
