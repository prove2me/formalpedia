-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolSuccessorHandoffInstrument_complete
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorHandoffInstrument_complete
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:41:53.594564+00:00
-- url     : https://prove2.me/theorems/212831c2-c82c-44a0-95a7-41aa30fa8a96
-- title:
--   HH18 Parameterized: decoded Retry Pool Successor Handoff Instrument complete
-- statement:
--   Completeness follows from the actual retry-pool completeness and the
--   chosen finite Kraus representation of the constructed CPTP handoff.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/HandoffInstrument.lean#L96-L116
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/HandoffInstrument.lean#L96-L116

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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorHandoffInstrument_complete {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z) :
    (decodedRetryPoolSuccessorHandoffInstrument h hdegree z q stage hstage).kraus.Complete := by sorry
