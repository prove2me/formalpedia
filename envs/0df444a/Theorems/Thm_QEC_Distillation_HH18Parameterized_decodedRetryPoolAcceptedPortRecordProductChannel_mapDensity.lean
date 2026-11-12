-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolAcceptedPortRecordProductChannel_mapDensity
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolAcceptedPortRecordProductChannel_mapDensity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:59:33.384348+00:00
-- url     : https://prove2.me/theorems/71cc0835-8894-47cc-a8e1-5cd264999157
-- title:
--   HH18 Parameterized: decoded Retry Pool Accepted Port Record Product Channel map Density
-- statement:
--   The fixed-port physical channel maps the genuine product of distinct
--   accepted blocks to the tensor product of their actual measurement records.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Records/AcceptedPortRecordProduct.lean#L100-L128
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Records/AcceptedPortRecordProduct.lean#L100-L128

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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolAcceptedPortRecordProductChannel_mapDensity
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0))
    (port : LogicalSite m w) (required : Nat) :
    (decodedRetryPoolAcceptedPortRecordProductChannel m w port required).mapDensity
        (decodedRetryPoolAcceptedProductDensity
          h hdegree epsilon rhoUnit required) =
      tensorPowerProductInput
        (decodedRetryPoolOneQubitRecordDensity
          (selectedLogicalPortRawParameter h hdegree epsilon port))
        rhoUnit required := by sorry
