-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolAcceptedPortRecordRegisterChannel_mapDensity
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolAcceptedPortRecordRegisterChannel_mapDensity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:01:28.377821+00:00
-- url     : https://prove2.me/theorems/ca21277f-537d-4893-89b6-d6d5c15354a7
-- title:
--   HH18 Parameterized: decoded Retry Pool Accepted Port Record Register Channel map Density
-- statement:
--   On the genuine product of distinct accepted parent blocks, the flattened
--   fixed-port channel produces the corresponding homogeneous record product.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/RecordRouting.lean#L162-L179
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/RecordRouting.lean#L162-L179

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Records_AcceptedPortRecordProduct
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Records_MeasuredRecordProduct
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_Routing
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_RecordRouting
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
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolAcceptedPortRecordRegisterChannel_mapDensity
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0))
    (port : LogicalSite m w) (required : Nat) :
    (decodedRetryPoolAcceptedPortRecordRegisterChannel
      m w port required).mapDensity
        (decodedRetryPoolAcceptedProductDensity
          h hdegree epsilon rhoUnit required) =
      decodedRetryPoolAcceptedPortRecordRegisterProductDensity
        m w (selectedLogicalPortRawParameter h hdegree epsilon port)
        rhoUnit required := by sorry
