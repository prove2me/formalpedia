-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolSuccessorRegroupBitstringEquiv_historyAt
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorRegroupBitstringEquiv_historyAt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:54:52.732665+00:00
-- url     : https://prove2.me/theorems/2c48f1a8-6923-4e6e-ab4f-13b759e9721d
-- title:
--   HH18 Parameterized: decoded Retry Pool Successor Regroup Bitstring Equiv history At
-- statement:
--   Selecting an outer history after regrouping retains exactly the complete
--   flat trial/physical record of the corresponding logical port.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/Regrouping.lean#L160-L181
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/Regrouping.lean#L160-L181

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_Measurement
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_Regrouping
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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorRegroupBitstringEquiv_historyAt
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (bits : Qubit.Bitstring
      (decodedRetryPoolSuccessorTargetSlots m w z q stage hstage))
    (branch : Fin (logicalOutputCount m w)) :
    tensorPowerHistoryAt
        (tensorPowerHistory (Qubit.Bitstring (PhysicalSite m w))
          (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩))
        (logicalOutputCount m w)
        (decodedRetryPoolSuccessorRegroupBitstringEquiv
          m w z q stage hstage bits) branch =
      decodedRetryPoolSuccessorPortTrialHistory
        m w z q stage hstage bits branch := by sorry
