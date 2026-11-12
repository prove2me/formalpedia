-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolPhysicalProtocolAcceptedCoordinateErrorMass_le_path
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalProtocolAcceptedCoordinateErrorMass_le_path
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T21:04:46.156202+00:00
-- url     : https://prove2.me/theorems/cc6255e4-f37c-4ea6-847b-afd264abc83f
-- title:
--   HH18 Parameterized: decoded Retry Pool Physical Protocol Accepted Coordinate Error Mass le path
-- statement:
--   Global success is contained in success along the nominated actual path,
--   so its measured terminal error mass is no larger.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/AcceptedError.lean#L99-L122
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/AcceptedError.lean#L99-L122

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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalProtocolAcceptedCoordinateErrorMass_le_path
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (hz : 0 < z)
    (rho : DensityOperator
      (decodedRetryPoolProtocolRootInputCarrier m w z q hz))
    (coordinate :
      decodedRetryPoolPhysicalProtocolOutputCoordinate m w z q hz) :
    decodedRetryPoolPhysicalProtocolAcceptedCoordinateErrorMass
        h hdegree z q hz rho coordinate <=
      Complex.re (LinearMap.trace Complex QubitSpace
        (aBasisInstrument.branchOperator .negative
          ((decodedRetryPoolAcceptedProductCoordinateChannel m w
            (decodedRetryPoolBackwardSchedule m w z q
              (decodedRetryPoolProtocolTerminalStage z hz))
            coordinate.2.1 coordinate.2.2)
            (decodedRetryPoolProtocolPathSuccessfulBranchOperatorGlobalAux
              h hdegree z q hz (z - 1) (by omega) coordinate.1 rho)))) := by sorry
