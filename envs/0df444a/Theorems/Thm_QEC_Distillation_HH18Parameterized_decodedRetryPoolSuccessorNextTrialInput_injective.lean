-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolSuccessorNextTrialInput_injective
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorNextTrialInput_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:15:26.679189+00:00
-- url     : https://prove2.me/theorems/0d0046c0-87ce-432d-894e-c452e0e6be6f
-- title:
--   HH18 Parameterized: decoded Retry Pool Successor Next Trial Input injective
-- statement:
--   Distinct selected blocks at a fixed logical branch route to distinct
--   next-stage trial coordinates.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/Routing.lean#L133-L147
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/Routing.lean#L133-L147

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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorNextTrialInput_injective
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (port : LogicalSite m w) :
    Function.Injective
      (decodedRetryPoolSuccessorNextTrialInput m w z q stage hstage port) := by sorry
