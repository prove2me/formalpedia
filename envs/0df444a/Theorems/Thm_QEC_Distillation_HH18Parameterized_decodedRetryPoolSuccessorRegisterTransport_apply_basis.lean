-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolSuccessorRegisterTransport_apply_basis
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorRegisterTransport_apply_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:14:25.609822+00:00
-- url     : https://prove2.me/theorems/c709a176-3217-4790-a9f9-fc6d3d6956bd
-- title:
--   HH18 Parameterized: decoded Retry Pool Successor Register Transport apply basis
-- statement:
--   The register transport maps every selected-output computational basis
--   vector to the computational basis vector of its exact successor coordinates.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/Routing.lean#L200-L210
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/Routing.lean#L200-L210

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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorRegisterTransport_apply_basis
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (bits : Qubit.Bitstring (decodedRetryPoolSuccessorSourceSlots m w z q stage)) :
    decodedRetryPoolSuccessorRegisterTransport m w z q stage hstage
      (EuclideanSpace.basisFun
        (Qubit.Bitstring (decodedRetryPoolSuccessorSourceSlots m w z q stage)) Complex bits) =
      EuclideanSpace.basisFun
        (Qubit.Bitstring (decodedRetryPoolSuccessorTargetSlots m w z q stage hstage)) Complex
        (decodedRetryPoolSuccessorBitstringEquiv m w z q stage hstage bits) := by sorry
