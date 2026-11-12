-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolNestedSuccessorStageInstrument_sum_bornWeight_eq_one
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolNestedSuccessorStageInstrument_sum_bornWeight_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:41:06.496027+00:00
-- url     : https://prove2.me/theorems/bffd3abb-1ab2-4141-ac0e-8a69023d5d28
-- title:
--   HH18 Parameterized: decoded Retry Pool Nested Successor Stage Instrument sum born Weight eq one
-- statement:
--   Every density input has normalized total observed mass under the complete
--   depth-indexed physical successor stage.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/NestedSuccessorStage.lean#L162-L175
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Successor/NestedSuccessorStage.lean#L162-L175

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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolNestedSuccessorStageInstrument_sum_bornWeight_eq_one
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (rho : DensityOperator
      (nestedTensorCarrier
        (QubitRegister (decodedRetryPoolSuccessorSourceSlots m w z q stage))
        (logicalOutputCount m w) stage.1)) :
    ∑ outcome,
        (decodedRetryPoolNestedSuccessorStageInstrument
          h hdegree z q stage hstage).bornWeight outcome rho = 1 := by sorry
