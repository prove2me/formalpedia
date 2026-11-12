-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolStageTransitionInstrument_observe
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolStageTransitionInstrument_observe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:39:24.820626+00:00
-- url     : https://prove2.me/theorems/dea6bb70-25c9-4327-8ef2-a2abf753f6c7
-- title:
--   HH18 Parameterized: decoded Retry Pool Stage Transition Instrument observe
-- statement:
--   The visible transition result is exactly the predecessor handoff outcome
--   followed by the actual observed histories of all next-stage pools.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Schedule/StageTransition.lean#L91-L114
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Schedule/StageTransition.lean#L91-L114

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_HandoffInstrument
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_StageTransition
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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolStageTransitionInstrument_observe {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (firstIndex : decodedRetryPoolSuccessorHandoffRawIndex
      h hdegree z q stage hstage)
    (secondHistory : decodedRetryPoolStageTransitionNextRawHistory
      h hdegree z q stage hstage) :
    (decodedRetryPoolStageTransitionInstrument h hdegree z q stage hstage).observe
        ⟨firstIndex, secondHistory⟩ =
      ⟨(decodedRetryPoolSuccessorHandoffInstrument
          h hdegree z q stage hstage).observe firstIndex,
        ((decodedRetryPoolInstrument h hdegree
          (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩)
          (decodedRetryPoolBackwardSchedule m w z q
            ⟨stage.1 + 1, hstage⟩)).tensorPower
              (logicalOutputCount m w)).observe secondHistory⟩ := by sorry
