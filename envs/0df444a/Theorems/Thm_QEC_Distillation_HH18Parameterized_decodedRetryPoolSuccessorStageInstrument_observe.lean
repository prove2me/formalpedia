-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolSuccessorStageInstrument_observe
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorStageInstrument_observe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:40:57.374044+00:00
-- url     : https://prove2.me/theorems/9be3028d-1f7a-40bd-8ad7-f7e7e6934474
-- title:
--   HH18 Parameterized: decoded Retry Pool Successor Stage Instrument observe
-- statement:
--   The one-path successor stage retains the unit channel observation and all
--   actual next-pool observations.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/NestedSuccessorStage.lean#L72-L98
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/NestedSuccessorStage.lean#L72-L98

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_StageTransition
import Definitions.Def_QEC_Semantics_Instruments_NestedTensor_Power
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_NestedSuccessorStage
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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorStageInstrument_observe {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (firstIndex : Fin
      ((decodedRetryPoolSuccessorNestedInputChannel m w z q stage hstage).chosenKrausCount))
    (secondHistory : tensorPowerHistory
      (decodedRetryPoolRawIndex h hdegree
        (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩)
        (decodedRetryPoolBackwardSchedule m w z q ⟨stage.1 + 1, hstage⟩))
      (logicalOutputCount m w)) :
    (decodedRetryPoolSuccessorStageInstrument h hdegree z q stage hstage).observe
        ⟨firstIndex, secondHistory⟩ =
      ⟨PUnit.unit,
        ((decodedRetryPoolInstrument h hdegree
          (decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩)
          (decodedRetryPoolBackwardSchedule m w z q
            ⟨stage.1 + 1, hstage⟩)).tensorPower
              (logicalOutputCount m w)).observe secondHistory⟩ := by sorry
