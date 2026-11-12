-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolSuccessorSourceSlots_card
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorSourceSlots_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:15:38.825276+00:00
-- url     : https://prove2.me/theorems/72e35e27-5e13-4e75-b2eb-f90d4718e8ca
-- title:
--   HH18 Parameterized: decoded Retry Pool Successor Source Slots card
-- statement:
--   The selected-output coordinate carrier has its literal selected-block and
--   logical-port cardinality.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/Routing.lean#L97-L101
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/Routing.lean#L97-L101

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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorSourceSlots_card
    (m w z q : Nat) (stage : Fin z) :
    Fintype.card (decodedRetryPoolSuccessorSourceSlots m w z q stage) =
      decodedRetryPoolBackwardSchedule m w z q stage * logicalOutputCount m w := by sorry
