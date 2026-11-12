-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolProtocolSuccessfulRoutingMassAux_zero_eq_enoughMass
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolSuccessfulRoutingMassAux_zero_eq_enoughMass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:26:37.719703+00:00
-- url     : https://prove2.me/theorems/e9c419b1-733d-4d57-95b9-930044019781
-- title:
--   HH18 Parameterized: decoded Retry Pool Protocol Successful Routing Mass Aux zero eq enough Mass
-- statement:
--   At the root, successful routing is exactly the actual decoded retry-pool
--   enough-history event.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/SuccessMassRecurrence.lean#L240-L263
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/SuccessMassRecurrence.lean#L240-L263

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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolSuccessfulRoutingMassAux_zero_eq_enoughMass
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (hz : 0 < z)
    (rho : DensityOperator (decodedRetryPoolProtocolRootInputCarrier m w z q hz)) :
    decodedRetryPoolProtocolSuccessfulRoutingMassAux
        h hdegree z q hz 0 hz rho =
      decodedRetryPoolEnoughMass h hdegree
        (decodedRetryPoolBackwardAttempts m w z q ⟨0, hz⟩)
        (decodedRetryPoolBackwardSchedule m w z q ⟨0, hz⟩) rho := by sorry
