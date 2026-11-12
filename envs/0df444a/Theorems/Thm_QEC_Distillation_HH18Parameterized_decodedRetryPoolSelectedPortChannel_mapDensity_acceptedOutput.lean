-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolSelectedPortChannel_mapDensity_acceptedOutput
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolSelectedPortChannel_mapDensity_acceptedOutput
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:57:28.314272+00:00
-- url     : https://prove2.me/theorems/07aae5ad-89a6-4f3a-b41d-c27f5019367d
-- title:
--   HH18 Parameterized: decoded Retry Pool Selected Port Channel map Density accepted Output
-- statement:
--   The selected-port channel returns the already-defined physical marginal
--   of the genuine accepted block.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Records/AcceptedPortRecordProduct.lean#L39-L47
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Records/AcceptedPortRecordProduct.lean#L39-L47

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Records_AcceptedProduct
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_Measurement
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_ChannelProduct
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Records_AcceptedPortRecordProduct
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open Semantics.FiniteInstrument
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolSelectedPortChannel_mapDensity_acceptedOutput
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (port : LogicalSite m w) :
    (decodedRetryPoolSelectedPortChannel m w port).mapDensity
        (resourceDecodedRun h hdegree
          (noisyResources m w epsilon)).acceptedOutput =
      selectedLogicalPortTransportedAcceptedOutput
        h hdegree epsilon port := by sorry
