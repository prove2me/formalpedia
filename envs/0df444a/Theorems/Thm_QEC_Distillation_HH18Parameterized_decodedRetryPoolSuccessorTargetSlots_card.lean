-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolSuccessorTargetSlots_card
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorTargetSlots_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:15:51.512366+00:00
-- url     : https://prove2.me/theorems/94b8ad65-7a37-487c-8cb2-1d6e648f99fc
-- title:
--   HH18 Parameterized: decoded Retry Pool Successor Target Slots card
-- statement:
--   The successor coordinate carrier has one logical branch for each next
--   retry attempt and each physical input coordinate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/Routing.lean#L105-L111
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/Routing.lean#L105-L111

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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorTargetSlots_card
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z) :
    Fintype.card (decodedRetryPoolSuccessorTargetSlots m w z q stage hstage) =
      logicalOutputCount m w *
        (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩ *
          physicalInputCount m w) := by sorry
