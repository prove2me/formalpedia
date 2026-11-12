-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolStageTransitionInstrument_sum_bornWeight_eq_one
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolStageTransitionInstrument_sum_bornWeight_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:40:38.844815+00:00
-- url     : https://prove2.me/theorems/cb9a6218-531f-4b5c-b78c-f35449f0bac7
-- title:
--   HH18 Parameterized: decoded Retry Pool Stage Transition Instrument sum born Weight eq one
-- statement:
--   Every physical input density has normalized total observed mass under the
--   complete two-stage transition.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Schedule/StageTransition.lean#L143-L153
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Schedule/StageTransition.lean#L143-L153

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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolStageTransitionInstrument_sum_bornWeight_eq_one
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (rho : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w)
        (decodedRetryPoolBackwardAttempts m w z q stage))) :
    ∑ outcome,
        (decodedRetryPoolStageTransitionInstrument h hdegree z q stage hstage).bornWeight
          outcome rho = 1 := by sorry
