-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolPhysicalExactBatchYield_eq_runSuccess
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalExactBatchYield_eq_runSuccess
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T21:06:09.142999+00:00
-- url     : https://prove2.me/theorems/7e0a0d3d-07cf-4745-b8b6-322ad4825dd4
-- title:
--   HH18 Parameterized: decoded Retry Pool Physical Exact Batch Yield eq run Success
-- statement:
--   The derived yield is definitionally the actual run success probability.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/Cost.lean#L62-L71
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/Cost.lean#L62-L71

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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalExactBatchYield_eq_runSuccess
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (depth : Nat)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    (decodedRetryPoolPhysicalExactBatchYield
        h hdegree epsilon depth rhoUnit : Real) =
      (decodedRetryPoolPhysicalExactBatchRun
        h hdegree epsilon depth rhoUnit).successProbability := by sorry
