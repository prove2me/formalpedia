-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolPhysicalExactBatchYield_pos
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalExactBatchYield_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T22:57:42.881551+00:00
-- url     : https://prove2.me/theorems/eb5737c8-42b3-45f6-bc64-3e978bd2746f
-- title:
--   HH18 Parameterized: decoded Retry Pool Physical Exact Batch Yield pos
-- statement:
--   The exact physical run yield is uniformly positive.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/Asymptotic.lean#L162-L174
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/Asymptotic.lean#L162-L174

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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalExactBatchYield_pos
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hpool : decodedRetryPoolInitialPoolingDomain w r m epsilon)
    (depth : Nat)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    0 < (decodedRetryPoolPhysicalExactBatchYield
      h hdegree epsilon depth rhoUnit : Real) := by sorry
