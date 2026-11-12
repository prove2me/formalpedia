-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolPhysicalProtocolRun_success_mul_coordinateError_eq_mass
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalProtocolRun_success_mul_coordinateError_eq_mass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T21:05:56.985543+00:00
-- url     : https://prove2.me/theorems/ad5d1f9d-182e-4b73-bc3d-cd4464d68f3d
-- title:
--   HH18 Parameterized: decoded Retry Pool Physical Protocol Run success mul coordinate Error eq mass
-- statement:
--   Weighting the genuine run's normalized coordinate error by its actual
--   success probability recovers the unnormalized global accepted-event mass.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/AcceptedError.lean#L171-L224
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/AcceptedError.lean#L171-L224

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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalProtocolRun_success_mul_coordinateError_eq_mass
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (z q : Nat) (hz : 0 < z)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0))
    (coordinate :
      decodedRetryPoolPhysicalProtocolOutputCoordinate m w z q hz) :
    (decodedRetryPoolPhysicalProtocolRun
        h hdegree epsilon z q hz rhoUnit).successProbability *
      decodedRetryPoolPhysicalProtocolCoordinateRawError m w z q hz coordinate
        (decodedRetryPoolPhysicalProtocolRun
          h hdegree epsilon z q hz rhoUnit).acceptedOutput =
      decodedRetryPoolPhysicalProtocolAcceptedCoordinateErrorMass
        h hdegree z q hz
          (decodedRetryPoolPhysicalProtocolNoisyRootInput
            m w z q hz epsilon rhoUnit) coordinate := by sorry
