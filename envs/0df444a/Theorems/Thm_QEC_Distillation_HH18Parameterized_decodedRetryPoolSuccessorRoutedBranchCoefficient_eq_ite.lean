-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolSuccessorRoutedBranchCoefficient_eq_ite
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorRoutedBranchCoefficient_eq_ite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:21:44.106522+00:00
-- url     : https://prove2.me/theorems/8b6d3779-cd2b-4268-923b-60ff794fe368
-- title:
--   HH18 Parameterized: decoded Retry Pool Successor Routed Branch Coefficient eq ite
-- statement:
--   The global branch coefficient is the same sibling-agreement indicator as
--   the direct coordinate-tensor coefficient.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/BranchProduct.lean#L563-L639
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/BranchProduct.lean#L563-L639

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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorRoutedBranchCoefficient_eq_ite
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (port : LogicalSite m w)
    (left right : Bitstring
      (decodedRetryPoolSuccessorSourceSlots m w z q stage)) :
    decodedRetryPoolSuccessorRoutedBranchCoefficient m w z q stage hstage
        (decodedRetryPoolLogicalSiteFinEquiv m w port) left right =
      if decodedRetryPoolSuccessorSiblingAgreement
          m w z q stage port left right then 1 else 0 := by sorry
