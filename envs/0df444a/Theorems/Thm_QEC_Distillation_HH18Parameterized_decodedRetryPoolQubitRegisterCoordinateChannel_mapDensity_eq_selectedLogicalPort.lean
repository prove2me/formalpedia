-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolQubitRegisterCoordinateChannel_mapDensity_eq_selectedLogicalPort
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolQubitRegisterCoordinateChannel_mapDensity_eq_selectedLogicalPort
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:24:21.996596+00:00
-- url     : https://prove2.me/theorems/9207e65f-db39-41e7-8911-3191436ce6d9
-- title:
--   HH18 Parameterized: decoded Retry Pool Qubit Register Coordinate Channel map Density eq selected Logical Port
-- statement:
--   The canonical tensor-coordinate operation is exactly the genuine
--   singleton finite-subsystem partial trace and basis transport used for one
--   logical output port.  The equality holds for every input density, including
--   joint outputs with correlations between sibling logical ports.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/Preparation.lean#L166-L307
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/Preparation.lean#L166-L307

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_Routing
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DepthTwoRouting
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_Basis
import Definitions.Def_QEC_Semantics_Instruments_Registers_Marginal
import Definitions.Def_QEC_Semantics_Channels_Instrument
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_Preparation
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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolQubitRegisterCoordinateChannel_mapDensity_eq_selectedLogicalPort
    (m w : Nat) (port : LogicalSite m w)
    (rho : DensityOperator (LogicalRegister m w)) :
    (decodedRetryPoolQubitRegisterCoordinateChannel
        (LogicalSite m w) port).mapDensity rho =
      (selectedLogicalPortTransport m w port).conjDensity
        ((selectedLogicalPortSubsystem m w port).selectedPartialTraceFromRegister.mapDensity
          rho) := by sorry
