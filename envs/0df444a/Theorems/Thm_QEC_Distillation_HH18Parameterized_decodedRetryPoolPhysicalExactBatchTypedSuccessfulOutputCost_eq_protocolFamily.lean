-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolPhysicalExactBatchTypedSuccessfulOutputCost_eq_protocolFamily
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalExactBatchTypedSuccessfulOutputCost_eq_protocolFamily
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T23:03:57.985212+00:00
-- url     : https://prove2.me/theorems/15bff4c5-39cf-4450-a2ef-e0f8262ace8b
-- title:
--   HH18 Parameterized: decoded Retry Pool Physical Exact Batch Typed Successful Output Cost eq protocol Family
-- statement:
--   The typed exact-batch cost is exactly the #458 successful-output cost of
--   the genuine pointwise family.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/Asymptotic.lean#L468-L495
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/Asymptotic.lean#L468-L495

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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalExactBatchTypedSuccessfulOutputCost_eq_protocolFamily
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hpool : decodedRetryPoolInitialPoolingDomain w r m epsilon)
    (depth : Nat)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    decodedRetryPoolPhysicalExactBatchTypedSuccessfulOutputCost
        h hdegree epsilon depth rhoUnit =
      (decodedRetryPoolPhysicalExactBatchProtocolFamily
        h hdegree epsilon hpool depth rhoUnit).successfulOutputCost PUnit.unit := by sorry
