-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolPhysicalExactBatchTypedSuccessfulOutputCost_le_sixteen_ninths
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalExactBatchTypedSuccessfulOutputCost_le_sixteen_ninths
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T21:07:59.591474+00:00
-- url     : https://prove2.me/theorems/1deb0bf0-9ead-4930-bd0e-c3286884d4e5
-- title:
--   HH18 Parameterized: decoded Retry Pool Physical Exact Batch Typed Successful Output Cost le sixteen ninths
-- statement:
--   The physical retry factor and actual success lower bound together give a
--   uniform `16/9` successful-output-cost factor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/Cost.lean#L168-L212
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/Cost.lean#L168-L212

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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalExactBatchTypedSuccessfulOutputCost_le_sixteen_ninths
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hpool : decodedRetryPoolInitialPoolingDomain w r m epsilon)
    (depth : Nat)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    decodedRetryPoolPhysicalExactBatchTypedSuccessfulOutputCost
        h hdegree epsilon depth rhoUnit <=
      (16 / 9 : Real) *
        ((physicalInputCount m w : Real) / logicalOutputCount m w) ^
          (depth + 1) := by sorry
