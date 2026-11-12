-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolSuccessorRoutedBranchChannel_eq_coordinateBranch
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorRoutedBranchChannel_eq_coordinateBranch
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:21:44.4975+00:00
-- url     : https://prove2.me/theorems/04cf4c1b-25a4-4e2b-9408-b6a552cd6f0c
-- title:
--   HH18 Parameterized: decoded Retry Pool Successor Routed Branch Channel eq coordinate Branch
-- statement:
--   The globally reindexed branch selector is exactly the direct physical
--   fixed-port successor channel, as channels on arbitrary source operators.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/BranchProduct.lean#L657-L699
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/BranchProduct.lean#L657-L699

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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorRoutedBranchChannel_eq_coordinateBranch
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (port : LogicalSite m w) :
    decodedRetryPoolSuccessorRoutedBranchChannel m w z q stage hstage
        (decodedRetryPoolLogicalSiteFinEquiv m w port) =
      decodedRetryPoolSuccessorCoordinateBranchChannel
        m w z q stage hstage port := by sorry
