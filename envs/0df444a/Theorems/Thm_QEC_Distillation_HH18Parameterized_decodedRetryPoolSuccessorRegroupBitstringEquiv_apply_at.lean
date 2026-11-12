-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolSuccessorRegroupBitstringEquiv_apply_at
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorRegroupBitstringEquiv_apply_at
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:33:07.956958+00:00
-- url     : https://prove2.me/theorems/fd514567-b6f6-4b28-9f80-752d06a07fe5
-- title:
--   HH18 Parameterized: decoded Retry Pool Successor Regroup Bitstring Equiv apply at
-- statement:
--   Coordinate-level meaning of the regrouping: outer tensor factor, inner
--   trial, and physical-site evaluation reads exactly the original flat bit.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/Regrouping.lean#L80-L142
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/Regrouping.lean#L80-L142

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_Measurement
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_Regrouping
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm

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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorRegroupBitstringEquiv_apply_at
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (bits : Qubit.Bitstring
      (decodedRetryPoolSuccessorTargetSlots m w z q stage hstage))
    (branch : Fin (logicalOutputCount m w))
    (trial : Fin
      (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩))
    (physical : PhysicalSite m w) :
    tensorPowerHistoryAt (Qubit.Bitstring (PhysicalSite m w))
      (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩)
      (tensorPowerHistoryAt
        (tensorPowerHistory (Qubit.Bitstring (PhysicalSite m w))
          (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩))
        (logicalOutputCount m w)
        (decodedRetryPoolSuccessorRegroupBitstringEquiv m w z q stage hstage bits)
        branch)
      trial physical =
    bits ((decodedRetryPoolLogicalSiteFinEquiv m w).symm branch,
      (trial, physical)) := by sorry
