-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolSuccessorOneQubitPreparation_selectedOutput
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorOneQubitPreparation_selectedOutput
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:26:31.323709+00:00
-- url     : https://prove2.me/theorems/70d94d7a-a8b4-4d69-a03a-23b8f2c54b6e
-- title:
--   HH18 Parameterized: decoded Retry Pool Successor One Qubit Preparation selected Output
-- statement:
--   On an actual accepted logical output port, the physical channel is
--   exactly the established dephased inverse-phase next-input construction.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/Preparation.lean#L387-L394
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/Preparation.lean#L387-L394

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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorOneQubitPreparation_selectedOutput
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (port : LogicalSite m w) :
    decodedRetryPoolSuccessorOneQubitPreparation.mapDensity
        (selectedLogicalPortTransportedAcceptedOutput h hdegree epsilon port) =
      selectedLogicalPortDephasedNextInput h hdegree epsilon port := by sorry
