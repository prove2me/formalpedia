-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolPhysicalExactBatchSuccessfulOutputCost_le_polylog
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalExactBatchSuccessfulOutputCost_le_polylog
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T22:58:20.91807+00:00
-- url     : https://prove2.me/theorems/4be018ae-27e1-4caf-a7c3-eccdc5e2eb1b
-- title:
--   HH18 Parameterized: decoded Retry Pool Physical Exact Batch Successful Output Cost le polylog
-- statement:
--   The exact physical run's successful-output cost has the required
--   polylogarithmic comparison at every dependent finite-depth index.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/Asymptotic.lean#L199-L254
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/Asymptotic.lean#L199-L254

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_Cost
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_Asymptotic
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open Semantics.FiniteInstrument
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalExactBatchSuccessfulOutputCost_le_polylog
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (hepsilon : 0 < epsilon.1)
    (hpool : decodedRetryPoolInitialPoolingDomain w r m epsilon)
    (depth : Nat)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    decodedRetryPoolPhysicalExactBatchTypedSuccessfulOutputCost
        h hdegree epsilon depth rhoUnit <=
      decodedRetryPoolPhysicalExactBatchScheduleCostCoefficient h epsilon *
        Real.rpow
          (Real.log (1 / routedDepthScheduleTargetError
            w r m epsilon (depth + 1)))
          (routedDepthScheduleGamma w r m) := by sorry
