-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolPhysicalProtocolAcceptedCoordinateErrorMass_eq
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalProtocolAcceptedCoordinateErrorMass_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T21:05:22.187624+00:00
-- url     : https://prove2.me/theorems/9822bc8c-f32e-4679-9170-1f86897727b1
-- title:
--   HH18 Parameterized: decoded Retry Pool Physical Protocol Accepted Coordinate Error Mass eq
-- statement:
--   The named accepted-coordinate mass unfolds to the physical instrument's
--   literal global-event filtered branch.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/AcceptedError.lean#L48-L70
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/AcceptedError.lean#L48-L70

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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalProtocolAcceptedCoordinateErrorMass_eq
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (hz : 0 < z)
    (rho : DensityOperator
      (decodedRetryPoolProtocolRootInputCarrier m w z q hz))
    (coordinate :
      decodedRetryPoolPhysicalProtocolOutputCoordinate m w z q hz) :
    decodedRetryPoolPhysicalProtocolAcceptedCoordinateErrorMass
        h hdegree z q hz rho coordinate =
      Complex.re (LinearMap.trace Complex QubitSpace
        (aBasisInstrument.branchOperator .negative
          ((decodedRetryPoolPhysicalProtocolTerminalCoordinateChannel
            m w z q hz coordinate)
            (filteredBranchOperatorSum
              (decodedRetryPoolPhysicalProtocolInstrument h hdegree z q hz)
              (fun outcome =>
                decodedRetryPoolPhysicalProtocolSuccessfulRouting
                  m w z q hz outcome = true)
              rho.toOperator)))) := by sorry
