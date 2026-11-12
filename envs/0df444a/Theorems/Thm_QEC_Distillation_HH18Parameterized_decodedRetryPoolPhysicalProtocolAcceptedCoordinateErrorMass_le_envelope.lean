-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolPhysicalProtocolAcceptedCoordinateErrorMass_le_envelope
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalProtocolAcceptedCoordinateErrorMass_le_envelope
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T21:06:29.023577+00:00
-- url     : https://prove2.me/theorems/1ba729cc-ee48-4d79-881e-7207226c03a5
-- title:
--   HH18 Parameterized: decoded Retry Pool Physical Protocol Accepted Coordinate Error Mass le envelope
-- statement:
--   Before normalization, the actual accepted-event error at every terminal
--   coordinate is bounded by the depth-`z` physical recurrence envelope.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/AcceptedError.lean#L228-L287
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/AcceptedError.lean#L228-L287

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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalProtocolAcceptedCoordinateErrorMass_le_envelope
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (z q : Nat) (hz : 0 < z)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0))
    (coordinate :
      decodedRetryPoolPhysicalProtocolOutputCoordinate m w z q hz) :
    decodedRetryPoolPhysicalProtocolAcceptedCoordinateErrorMass
        h hdegree z q hz
          (decodedRetryPoolPhysicalProtocolNoisyRootInput
            m w z q hz epsilon rhoUnit) coordinate <=
      routedDepthErrorEnvelope w r m epsilon z := by sorry
