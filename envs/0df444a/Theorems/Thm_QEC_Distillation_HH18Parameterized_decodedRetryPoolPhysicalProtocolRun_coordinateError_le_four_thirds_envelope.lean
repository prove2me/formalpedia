-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolPhysicalProtocolRun_coordinateError_le_four_thirds_envelope
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalProtocolRun_coordinateError_le_four_thirds_envelope
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T21:05:56.748079+00:00
-- url     : https://prove2.me/theorems/06c0a527-9383-4c0e-9cbb-e71dc0e875cb
-- title:
--   HH18 Parameterized: decoded Retry Pool Physical Protocol Run coordinate Error le four thirds envelope
-- statement:
--   Every actual terminal coordinate of the normalized physical run has
--   negative-A error at most `4/3` times the depth-`z` distance-power envelope.
--   The factor is solely the reciprocal of the proved global success lower bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/AcceptedError.lean#L292-L328
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/AcceptedError.lean#L292-L328

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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalProtocolRun_coordinateError_le_four_thirds_envelope
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hpool : decodedRetryPoolInitialPoolingDomain w r m epsilon)
    (z q : Nat) (hz : 0 < z)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0))
    (coordinate :
      decodedRetryPoolPhysicalProtocolOutputCoordinate m w z q hz) :
    decodedRetryPoolPhysicalProtocolCoordinateRawError m w z q hz coordinate
        (decodedRetryPoolPhysicalProtocolRun
          h hdegree epsilon z q hz rhoUnit).acceptedOutput <=
      (4 / 3 : Real) * routedDepthErrorEnvelope w r m epsilon z := by sorry
