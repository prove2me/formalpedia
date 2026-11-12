-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolSuccessorSlots_card_eq
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorSlots_card_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:17:30.16791+00:00
-- url     : https://prove2.me/theorems/e495edae-8071-4332-9234-bb4990b27053
-- title:
--   HH18 Parameterized: decoded Retry Pool Successor Slots card eq
-- statement:
--   The derived lossless route proves equality of the source and successor
--   coordinate cardinalities.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/Routing.lean#L115-L119
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/Routing.lean#L115-L119

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_BackwardSchedule
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_Routing
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorSlots_card_eq
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z) :
    Fintype.card (decodedRetryPoolSuccessorSourceSlots m w z q stage) =
      Fintype.card (decodedRetryPoolSuccessorTargetSlots m w z q stage hstage) := by sorry
