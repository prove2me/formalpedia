-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolSuccessorOneQubitRecordChannel_selectedOutput
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorOneQubitRecordChannel_selectedOutput
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:30:55.896748+00:00
-- url     : https://prove2.me/theorems/937592cb-0753-4968-81ed-d25b5963cee9
-- title:
--   HH18 Parameterized: decoded Retry Pool Successor One Qubit Record Channel selected Output
-- statement:
--   On an actual accepted logical output, the complete physical successor
--   channel produces the computational record at its measured error parameter.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/Measurement.lean#L107-L118
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/Measurement.lean#L107-L118

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_Preparation
import Definitions.Def_QEC_Semantics_Instruments_Registers_ChannelProduct
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_Measurement
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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorOneQubitRecordChannel_selectedOutput
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (port : LogicalSite m w) :
    decodedRetryPoolSuccessorOneQubitRecordChannel.mapDensity
        (selectedLogicalPortTransportedAcceptedOutput h hdegree epsilon port) =
      decodedRetryPoolOneQubitRecordDensity
        (selectedLogicalPortRawParameter h hdegree epsilon port) := by sorry
