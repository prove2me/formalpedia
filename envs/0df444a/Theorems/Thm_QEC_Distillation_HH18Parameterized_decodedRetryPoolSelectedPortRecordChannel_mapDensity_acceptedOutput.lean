-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolSelectedPortRecordChannel_mapDensity_acceptedOutput
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolSelectedPortRecordChannel_mapDensity_acceptedOutput
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:57:29.854605+00:00
-- url     : https://prove2.me/theorems/044eba42-913c-41f2-8b20-0ab7f37a9426
-- title:
--   HH18 Parameterized: decoded Retry Pool Selected Port Record Channel map Density accepted Output
-- statement:
--   On the genuine normalized accepted output, the selected-port channel
--   produces its literal computational clean/error record.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Records/AcceptedPortRecordProduct.lean#L60-L72
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Records/AcceptedPortRecordProduct.lean#L60-L72

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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolSelectedPortRecordChannel_mapDensity_acceptedOutput
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (port : LogicalSite m w) :
    (decodedRetryPoolSelectedPortRecordChannel m w port).mapDensity
        (resourceDecodedRun h hdegree
          (noisyResources m w epsilon)).acceptedOutput =
      decodedRetryPoolOneQubitRecordDensity
        (selectedLogicalPortRawParameter h hdegree epsilon port) := by sorry
