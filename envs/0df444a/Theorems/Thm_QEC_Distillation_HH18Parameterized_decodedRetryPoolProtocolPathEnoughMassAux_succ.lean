-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolProtocolPathEnoughMassAux_succ
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolPathEnoughMassAux_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:09:56.273671+00:00
-- url     : https://prove2.me/theorems/e5de64f2-76bc-411b-be6a-0a4c99a414bc
-- title:
--   HH18 Parameterized: decoded Retry Pool Protocol Path Enough Mass Aux succ
-- statement:
--   The HH18 Parameterized construction uses the decoded Retry Pool Protocol Path Enough Mass Aux succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Paths/BranchOperator.lean#L103-L131
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Paths/BranchOperator.lean#L103-L131

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Paths_SuccessEvent
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_SuccessMassRecurrence
import Definitions.Def_QEC_Semantics_Instruments_Sequential_NestedFilteredMarginalBranchOperator
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Paths_BranchOperator
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

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolPathEnoughMassAux_succ
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (z q stage : Nat) (hstage : stage + 1 < z)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0))
    (path : routedDepthOutputSlots m w (stage + 1)) :
    decodedRetryPoolProtocolPathEnoughMassAux
        h hdegree epsilon hsmall z q rhoUnit (stage + 1) hstage path =
      decodedRetryPoolProtocolPathEnoughMassAux
          h hdegree epsilon hsmall z q rhoUnit stage (by omega)
            (routedDepthOutputPathInit m w stage path) *
        decodedRetryPoolEnoughMass h hdegree
          (decodedRetryPoolBackwardAttempts m w z q
            ⟨stage + 1, hstage⟩)
          (decodedRetryPoolBackwardSchedule m w z q
            ⟨stage + 1, hstage⟩)
          (decodedRetryPoolSuccessorStageSelectedNextInput
            h hdegree
            (routedDepthPathRate h hdegree epsilon hsmall stage
              (routedDepthOutputPathInit m w stage path))
            z q ⟨stage, by omega⟩ hstage
            (routedDepthOutputPathLast m w stage path)
            (routedDepthPathNextHalf h hdegree epsilon hsmall
              (routedDepthOutputPathInit m w stage path)
              (routedDepthOutputPathLast m w stage path))
            rhoUnit) := by sorry

attribute [defeq] QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolPathEnoughMassAux_succ
