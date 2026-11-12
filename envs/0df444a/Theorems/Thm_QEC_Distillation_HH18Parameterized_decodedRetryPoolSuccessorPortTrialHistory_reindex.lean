-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolSuccessorPortTrialHistory_reindex
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorPortTrialHistory_reindex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:54:58.287338+00:00
-- url     : https://prove2.me/theorems/1044fc56-d9da-41d5-94a0-347589ff1394
-- title:
--   HH18 Parameterized: decoded Retry Pool Successor Port Trial History reindex
-- statement:
--   The recursive successor-trial history selected from a routed source label
--   is exactly the fixed logical port's selected-block record, reindexed through
--   the compiled attempt/physical-slot equivalence.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/Regrouping.lean#L398-L420
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/Regrouping.lean#L398-L420

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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorPortTrialHistory_reindex
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (bits : Qubit.Bitstring
      (decodedRetryPoolSuccessorSourceSlots m w z q stage))
    (branch : Fin (logicalOutputCount m w)) :
    decodedRetryPoolSuccessorPortTrialHistory m w z q stage hstage
        (decodedRetryPoolSuccessorBitstringEquiv
          m w z q stage hstage bits) branch =
      (tensorPowerQubitBitstringEquiv (PhysicalSite m w)
        (decodedRetryPoolBackwardAttempts m w z q
          ⟨stage.1 + 1, hstage⟩)).symm
        (fun coordinate =>
          bits
            ((decodedRetryPoolSuccessorAttemptSlotsEquiv
              m w z q stage hstage).symm coordinate,
              (decodedRetryPoolLogicalSiteFinEquiv m w).symm branch)) := by sorry
