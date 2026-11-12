-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolProtocolRootSuccessfulBranchOperator_eq
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolRootSuccessfulBranchOperator_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:26:34.694888+00:00
-- url     : https://prove2.me/theorems/be8c3e36-5e85-45eb-9afc-56ccda5174b0
-- title:
--   HH18 Parameterized: decoded Retry Pool Protocol Root Successful Branch Operator eq
-- statement:
--   On the genuine noisy root input, the root successful-event operator is
--   the measured root enough mass times the accepted-product density.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Paths/BranchOperator.lean#L367-L387
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Paths/BranchOperator.lean#L367-L387

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Paths_SuccessEvent
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_SuccessMassRecurrence
import Definitions.Def_QEC_Semantics_Instruments_Sequential_NestedFilteredMarginalBranchOperator
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Paths_BranchOperator
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open Semantics.FiniteInstrument
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolRootSuccessfulBranchOperator_eq
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (z q : Nat) (hz : 0 < z)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    decodedRetryPoolProtocolRootSuccessfulBranchOperator h hdegree z q hz
        (decodedRetryPoolPhysicalProtocolNoisyRootInput
          m w z q hz epsilon rhoUnit) =
      (decodedRetryPoolEnoughMass h hdegree
        (decodedRetryPoolBackwardAttempts m w z q ⟨0, hz⟩)
        (decodedRetryPoolBackwardSchedule m w z q ⟨0, hz⟩)
        (decodedRetryPoolPhysicalProtocolNoisyRootInput
          m w z q hz epsilon rhoUnit) : Complex) •
        (decodedRetryPoolAcceptedProductDensity h hdegree epsilon rhoUnit
          (decodedRetryPoolBackwardSchedule m w z q ⟨0, hz⟩)).toOperator := by sorry
