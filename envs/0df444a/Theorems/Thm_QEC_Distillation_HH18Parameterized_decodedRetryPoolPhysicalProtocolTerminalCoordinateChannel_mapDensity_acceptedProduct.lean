-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolPhysicalProtocolTerminalCoordinateChannel_mapDensity_acceptedProduct
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalProtocolTerminalCoordinateChannel_mapDensity_acceptedProduct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T21:04:29.7192+00:00
-- url     : https://prove2.me/theorems/b190d2b4-3895-4d50-84e5-7ac59dc6b9d5
-- title:
--   HH18 Parameterized: decoded Retry Pool Physical Protocol Terminal Coordinate Channel map Density accepted Product
-- statement:
--   Evaluating the terminal block/port part of the physical coordinate on a
--   genuine accepted product returns the selected one-level accepted output.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/OutputCoordinate.lean#L113-L131
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/OutputCoordinate.lean#L113-L131

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_Run
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_Accounting
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Records_AcceptedPortRecordProduct
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_OutputCoordinate
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
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalProtocolTerminalCoordinateChannel_mapDensity_acceptedProduct
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (z q : Nat) (hz : 0 < z)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0))
    (coordinate :
      decodedRetryPoolPhysicalProtocolOutputCoordinate m w z q hz) :
    (decodedRetryPoolAcceptedProductCoordinateChannel m w
      (decodedRetryPoolBackwardSchedule m w z q
        (decodedRetryPoolProtocolTerminalStage z hz))
      coordinate.2.1 coordinate.2.2).mapDensity
        (decodedRetryPoolAcceptedProductDensity h hdegree epsilon rhoUnit
          (decodedRetryPoolBackwardSchedule m w z q
            (decodedRetryPoolProtocolTerminalStage z hz))) =
      selectedLogicalPortTransportedAcceptedOutput
        h hdegree epsilon coordinate.2.2 := by sorry
