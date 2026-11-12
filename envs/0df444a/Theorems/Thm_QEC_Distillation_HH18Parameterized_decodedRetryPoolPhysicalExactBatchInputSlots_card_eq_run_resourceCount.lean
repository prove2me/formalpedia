-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolPhysicalExactBatchInputSlots_card_eq_run_resourceCount
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalExactBatchInputSlots_card_eq_run_resourceCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T21:06:43.316813+00:00
-- url     : https://prove2.me/theorems/e0ad8849-7036-4ec7-b31c-cb356f897f06
-- title:
--   HH18 Parameterized: decoded Retry Pool Physical Exact Batch Input Slots card eq run resource Count
-- statement:
--   The literal input-slot cardinality is the resource count stored by the
--   same genuine run.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/Cost.lean#L75-L84
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/Cost.lean#L75-L84

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_ExactBatching
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_AcceptedError
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_Cost
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.FiniteInstrument
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalExactBatchInputSlots_card_eq_run_resourceCount
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (depth : Nat)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    Fintype.card (decodedRetryPoolPhysicalExactBatchInputSlots m w depth) =
      (decodedRetryPoolPhysicalExactBatchRun
        h hdegree epsilon depth rhoUnit).resourceCount := by sorry
