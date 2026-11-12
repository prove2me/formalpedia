-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolProtocolPathSuccessfulBranchOperatorAux_eq_mass_smul_acceptedProduct
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolPathSuccessfulBranchOperatorAux_eq_mass_smul_acceptedProduct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:26:44.200032+00:00
-- url     : https://prove2.me/theorems/5bd9e8a9-909f-44de-b04a-47b0874a4e16
-- title:
--   HH18 Parameterized: decoded Retry Pool Protocol Path Successful Branch Operator Aux eq mass smul accepted Product
-- statement:
--   Every successful physical routed-path branch is its recursively measured
--   enough mass multiplying the genuine accepted-product density at that path's
--   actual reached rate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Paths/BranchOperator.lean#L523-L547
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Paths/BranchOperator.lean#L523-L547

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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolPathSuccessfulBranchOperatorAux_eq_mass_smul_acceptedProduct
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (z q : Nat) (hz : 0 < z)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    ∀ (stage : Nat) (hstage : stage < z)
      (path : routedDepthOutputSlots m w stage),
      decodedRetryPoolProtocolPathSuccessfulBranchOperatorAux
          h hdegree z q hz
            (decodedRetryPoolPhysicalProtocolNoisyRootInput
              m w z q hz epsilon rhoUnit)
            stage hstage path =
        (decodedRetryPoolProtocolPathEnoughMassAux
          h hdegree epsilon hsmall z q rhoUnit stage hstage path : Complex) •
          (decodedRetryPoolAcceptedProductDensity h hdegree
            (routedDepthPathRate h hdegree epsilon hsmall stage path)
            rhoUnit
            (decodedRetryPoolBackwardSchedule m w z q
              ⟨stage, hstage⟩)).toOperator := by sorry
