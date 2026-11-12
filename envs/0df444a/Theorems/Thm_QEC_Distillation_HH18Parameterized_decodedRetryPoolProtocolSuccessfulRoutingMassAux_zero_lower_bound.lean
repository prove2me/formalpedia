-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolProtocolSuccessfulRoutingMassAux_zero_lower_bound
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolSuccessfulRoutingMassAux_zero_lower_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:26:06.541737+00:00
-- url     : https://prove2.me/theorems/f3dd6caf-a240-4397-8398-5793a33c26c1
-- title:
--   HH18 Parameterized: decoded Retry Pool Protocol Successful Routing Mass Aux zero lower bound
-- statement:
--   The physical root's good-routing mass satisfies the exact stage-zero
--   dyadic shortage bound on the genuine noisy product input.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/SuccessMassRecurrence.lean#L267-L284
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/SuccessMassRecurrence.lean#L267-L284

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_BornMass
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_BranchProduct
import Definitions.Def_QEC_Semantics_Instruments_Tensor_MarginalBornMass
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BranchOperator
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_SuccessMassRecurrence
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.FiniteInstrument
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
attribute [local instance] QEC.Distillation.HH18Parameterized.instPhysicalSuccessMassRecurrenceClassicalDecidable
attribute [local instance] QEC.Distillation.HH18Parameterized.instPhysicalSuccessMassRecurrenceClassicalDecidable

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolSuccessfulRoutingMassAux_zero_lower_bound
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (hz : 0 < z)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (rhoUnit : DensityOperator (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    1 - decodedRetryPoolStageAggregateShortageBudget w r m epsilon 0 <=
      decodedRetryPoolProtocolSuccessfulRoutingMassAux
        h hdegree z q hz 0 hz
          (decodedRetryPoolPhysicalProtocolNoisyRootInput
            m w z q hz epsilon rhoUnit) := by sorry
