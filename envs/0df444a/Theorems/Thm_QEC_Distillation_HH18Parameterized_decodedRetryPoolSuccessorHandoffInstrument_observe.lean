-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolSuccessorHandoffInstrument_observe
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorHandoffInstrument_observe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:38:37.258224+00:00
-- url     : https://prove2.me/theorems/25ac4355-dfe0-4fbc-938a-ef90b069a150
-- title:
--   HH18 Parameterized: decoded Retry Pool Successor Handoff Instrument observe
-- statement:
--   The handoff observation is precisely the current pool observation followed
--   by the unit observation of the physical successor channel.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/HandoffInstrument.lean#L65-L92
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/HandoffInstrument.lean#L65-L92

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_Regrouping
import Definitions.Def_QEC_Semantics_Channels_Instrument
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_HandoffInstrument
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open Semantics.FiniteInstrument
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorHandoffInstrument_observe {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (firstIndex : decodedRetryPoolRawIndex h hdegree
      (decodedRetryPoolBackwardAttempts m w z q stage)
      (decodedRetryPoolBackwardSchedule m w z q stage))
    (secondIndex : Fin
      ((decodedRetryPoolSuccessorNestedInputChannel m w z q stage hstage).chosenKrausCount)) :
    (decodedRetryPoolSuccessorHandoffInstrument h hdegree z q stage hstage).observe
        ⟨firstIndex, secondIndex⟩ =
      ⟨(decodedRetryPoolInstrument h hdegree
          (decodedRetryPoolBackwardAttempts m w z q stage)
          (decodedRetryPoolBackwardSchedule m w z q stage)).observe firstIndex,
        PUnit.unit⟩ := by sorry
