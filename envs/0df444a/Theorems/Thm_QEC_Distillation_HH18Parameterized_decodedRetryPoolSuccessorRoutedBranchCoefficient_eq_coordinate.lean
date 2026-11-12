-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolSuccessorRoutedBranchCoefficient_eq_coordinate
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorRoutedBranchCoefficient_eq_coordinate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:21:21.133282+00:00
-- url     : https://prove2.me/theorems/b7b36fcc-bdae-4f38-a197-d84f92f05492
-- title:
--   HH18 Parameterized: decoded Retry Pool Successor Routed Branch Coefficient eq coordinate
-- statement:
--   The global and direct physical fixed-port selectors have identical
--   coefficients on every source computational matrix unit.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/BranchProduct.lean#L643-L653
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/BranchProduct.lean#L643-L653

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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorRoutedBranchCoefficient_eq_coordinate
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (port : LogicalSite m w)
    (left right : Bitstring
      (decodedRetryPoolSuccessorSourceSlots m w z q stage)) :
    decodedRetryPoolSuccessorRoutedBranchCoefficient m w z q stage hstage
        (decodedRetryPoolLogicalSiteFinEquiv m w port) left right =
      decodedRetryPoolSuccessorCoordinateBranchCoefficient
        m w z q stage port left right := by sorry
