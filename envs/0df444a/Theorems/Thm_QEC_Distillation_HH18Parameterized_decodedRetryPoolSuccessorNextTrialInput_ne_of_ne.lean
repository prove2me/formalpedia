-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolSuccessorNextTrialInput_ne_of_ne
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorNextTrialInput_ne_of_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:17:05.601754+00:00
-- url     : https://prove2.me/theorems/7f9a9cdc-aec6-44d5-9e90-5bee835f91d0
-- title:
--   HH18 Parameterized: decoded Retry Pool Successor Next Trial Input ne of ne
-- statement:
--   Unequal selected blocks at a fixed logical branch retain distinct
--   next-stage trial coordinates.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/Routing.lean#L151-L160
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/Routing.lean#L151-L160

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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorNextTrialInput_ne_of_ne
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (port : LogicalSite m w)
    {left right : Fin (decodedRetryPoolBackwardSchedule m w z q stage)}
    (hne : left ≠ right) :
    decodedRetryPoolSuccessorNextTrialInput m w z q stage hstage port left ≠
      decodedRetryPoolSuccessorNextTrialInput m w z q stage hstage port right := by sorry
