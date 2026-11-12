-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolQubitRegisterCoordinateChannel_mapDensity_sitewise
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolQubitRegisterCoordinateChannel_mapDensity_sitewise
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:25:40.167202+00:00
-- url     : https://prove2.me/theorems/2ecda653-e2a3-40e5-859f-d10da8be99a8
-- title:
--   HH18 Parameterized: decoded Retry Pool Qubit Register Coordinate Channel map Density sitewise
-- statement:
--   A homogeneous sitewise channel cannot signal into a nominated coordinate:
--   the retained output is exactly the one-qubit channel applied to the true
--   retained input, even for a correlated register density.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/Preparation.lean#L312-L364
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/Preparation.lean#L312-L364

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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolQubitRegisterCoordinateChannel_mapDensity_sitewise
    (channel : QuantumChannel QubitSpace QubitSpace)
    (ι : Type) [Fintype ι] [DecidableEq ι]
    (site : ι) (rho : DensityOperator (QubitRegister ι)) :
    (decodedRetryPoolQubitRegisterCoordinateChannel ι site).mapDensity
        ((decodedRetryPoolQubitRegisterSitewiseChannel channel ι).mapDensity rho) =
      channel.mapDensity
        ((decodedRetryPoolQubitRegisterCoordinateChannel ι site).mapDensity rho) := by sorry
