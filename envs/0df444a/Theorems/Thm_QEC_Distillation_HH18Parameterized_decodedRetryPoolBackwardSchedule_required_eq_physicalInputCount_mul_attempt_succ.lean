-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolBackwardSchedule_required_eq_physicalInputCount_mul_attempt_succ
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolBackwardSchedule_required_eq_physicalInputCount_mul_attempt_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:08:59.413114+00:00
-- url     : https://prove2.me/theorems/1a2ff90c-0fde-4e0f-8419-f431e8829ce7
-- title:
--   HH18 Parameterized: decoded Retry Pool Backward Schedule required eq physical Input Count mul attempt succ
-- statement:
--   Every nonterminal forward stage requests one physical block for each
--   retry attempt at its immediate successor.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Schedule/BackwardSchedule.lean#L51-L71
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Schedule/BackwardSchedule.lean#L51-L71

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_DyadicSlack
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_BackwardSchedule
set_option autoImplicit false
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding
open Coding.ReedMuller Coding.PuncturedReedMuller
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolBackwardSchedule_required_eq_physicalInputCount_mul_attempt_succ
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z) :
    decodedRetryPoolBackwardSchedule m w z q stage =
      physicalInputCount m w *
        decodedRetryPoolBackwardAttempts m w z q ⟨stage.1 + 1, hstage⟩ := by sorry
