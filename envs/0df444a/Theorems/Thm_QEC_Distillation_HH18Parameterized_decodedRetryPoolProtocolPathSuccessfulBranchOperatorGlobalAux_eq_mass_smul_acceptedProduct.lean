-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalAux_eq_mass_smul_acceptedProduct
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalAux_eq_mass_smul_acceptedProduct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:14:59.74013+00:00
-- url     : https://prove2.me/theorems/75dfa80a-7182-4fff-9034-b064b28ad943
-- title:
--   HH18 Parameterized: decoded Retry Pool Protocol Path Successful Branch Operator Global Aux eq mass smul accepted Product
-- statement:
--   Consequently the original whole-history selected path event is its
--   measured enough-mass product times the genuine reached accepted product.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Paths/GlobalBridge.lean#L320-L345
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Paths/GlobalBridge.lean#L320-L345

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Paths_BranchOperator
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Paths_GlobalBridge
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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalAux_eq_mass_smul_acceptedProduct
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (z q : Nat) (hz : 0 < z)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    ∀ (stage : Nat) (hstage : stage < z)
      (path : routedDepthOutputSlots m w stage),
      decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalAux
          h hdegree z q hz stage hstage path
            (decodedRetryPoolPhysicalProtocolNoisyRootInput
              m w z q hz epsilon rhoUnit) =
        (decodedRetryPoolProtocolPathEnoughMassAux
          h hdegree epsilon hsmall z q rhoUnit stage hstage path : Complex) •
          (decodedRetryPoolAcceptedProductDensity h hdegree
            (routedDepthPathRate h hdegree epsilon hsmall stage path)
            rhoUnit
            (decodedRetryPoolBackwardSchedule m w z q
              ⟨stage, hstage⟩)).toOperator := by sorry
