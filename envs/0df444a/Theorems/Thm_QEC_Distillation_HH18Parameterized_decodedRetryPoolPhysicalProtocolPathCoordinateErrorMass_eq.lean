-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolPhysicalProtocolPathCoordinateErrorMass_eq
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalProtocolPathCoordinateErrorMass_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T21:04:43.0542+00:00
-- url     : https://prove2.me/theorems/4a84f8dd-c80a-4fa8-b685-7ca6de1c5a1d
-- title:
--   HH18 Parameterized: decoded Retry Pool Physical Protocol Path Coordinate Error Mass eq
-- statement:
--   The measured error on a successful terminal path is its actual path Born
--   mass times the genuine selected-port raw error at the reached physical rate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/AcceptedError.lean#L126-L167
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/AcceptedError.lean#L126-L167

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_OutputCoordinate
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Paths_GlobalBridge
import Definitions.Def_QEC_Semantics_Instruments_Branches_FilteredBranchMeasurement
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_AcceptedError
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open Semantics.FiniteInstrument
open Triorthogonal.BH12NoisyInjection
open Triorthogonal.BH12NoisyInjection.OneQubit
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalProtocolPathCoordinateErrorMass_eq
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (z q : Nat) (hz : 0 < z)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0))
    (coordinate :
      decodedRetryPoolPhysicalProtocolOutputCoordinate m w z q hz) :
    Complex.re (LinearMap.trace Complex QubitSpace
        (aBasisInstrument.branchOperator .negative
          ((decodedRetryPoolAcceptedProductCoordinateChannel m w
            (decodedRetryPoolBackwardSchedule m w z q
              (decodedRetryPoolProtocolTerminalStage z hz))
            coordinate.2.1 coordinate.2.2)
            (decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalAux
              h hdegree z q hz (z - 1) (by omega) coordinate.1
              (decodedRetryPoolPhysicalProtocolNoisyRootInput
                m w z q hz epsilon rhoUnit))))) =
      decodedRetryPoolProtocolPathEnoughMassAux
          h hdegree epsilon hsmall z q rhoUnit (z - 1) (by omega)
            coordinate.1 *
        selectedLogicalPortRawError h hdegree
          (routedDepthPathRate h hdegree epsilon hsmall (z - 1)
            coordinate.1) coordinate.2.2 := by sorry
