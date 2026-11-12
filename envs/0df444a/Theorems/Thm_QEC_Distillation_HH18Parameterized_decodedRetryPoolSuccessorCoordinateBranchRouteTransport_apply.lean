-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolSuccessorCoordinateBranchRouteTransport_apply
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorCoordinateBranchRouteTransport_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:47:07.990047+00:00
-- url     : https://prove2.me/theorems/dd5cbd53-9b5b-49af-94c5-6f019b0a42ad
-- title:
--   HH18 Parameterized: decoded Retry Pool Successor Coordinate Branch Route Transport apply
-- statement:
--   The HH18 Parameterized construction uses the decoded Retry Pool Successor Coordinate Branch Route Transport apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/BranchProduct.lean#L78-L90
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/BranchProduct.lean#L78-L90

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_Regrouping
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_RecordRouting
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_ChannelProductFunctorial
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_BranchProduct
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm

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
attribute [local instance] QEC.Distillation.HH18Parameterized.instSuccessorBranchClassicalDecidable
attribute [local instance] QEC.Distillation.HH18Parameterized.instSuccessorBranchClassicalDecidable

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorCoordinateBranchRouteTransport_apply
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (x : tensorPowerCarrier QubitSpace
      (decodedRetryPoolBackwardSchedule m w z q stage)) :
    decodedRetryPoolSuccessorCoordinateBranchRouteTransport
        m w z q stage hstage x =
      (tensorPowerQubitRegisterTransport (PhysicalSite m w)
        (decodedRetryPoolBackwardAttempts m w z q
          ⟨stage.1 + 1, hstage⟩)).symm
        (decodedRetryPoolSuccessorPortRecordTransport m w z q stage hstage
          (decodedRetryPoolQubitTensorPowerFinRegisterTransport
            (decodedRetryPoolBackwardSchedule m w z q stage) x)) := by sorry

attribute [defeq] QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorCoordinateBranchRouteTransport_apply
