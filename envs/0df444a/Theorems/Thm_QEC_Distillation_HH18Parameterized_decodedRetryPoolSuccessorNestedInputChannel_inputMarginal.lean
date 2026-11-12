-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolSuccessorNestedInputChannel_inputMarginal
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorNestedInputChannel_inputMarginal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:23:05.424199+00:00
-- url     : https://prove2.me/theorems/2cb9be47-d6da-4360-aaf2-ea39471c3ea3
-- title:
--   HH18 Parameterized: decoded Retry Pool Successor Nested Input Channel input Marginal
-- statement:
--   The true marginal of the actual globally regrouped successor input is
--   the corresponding physical routed-branch channel applied after the genuine
--   sitewise record preparation.  This is a no-signalling statement about one
--   coordinate of the joint successor state; it does not assert that distinct
--   logical branches are independent.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/BranchProduct.lean#L706-L722
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/BranchProduct.lean#L706-L722

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_Regrouping
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_RecordRouting
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_ChannelProductFunctorial
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_BranchProduct
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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorNestedInputChannel_inputMarginal
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (rho : DensityOperator (QubitRegister
      (decodedRetryPoolSuccessorSourceSlots m w z q stage)))
    (branch : Fin (logicalOutputCount m w)) :
    tensorPowerInputMarginal (logicalOutputCount m w)
        ((decodedRetryPoolSuccessorNestedInputChannel
          m w z q stage hstage).mapDensity rho) branch =
      (decodedRetryPoolSuccessorRoutedBranchChannel
        m w z q stage hstage branch).mapDensity
          ((decodedRetryPoolSuccessorRecordPreparationChannel
            m w z q stage).mapDensity rho) := by sorry
