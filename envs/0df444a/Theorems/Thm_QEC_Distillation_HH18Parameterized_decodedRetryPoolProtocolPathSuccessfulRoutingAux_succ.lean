-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolProtocolPathSuccessfulRoutingAux_succ
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolPathSuccessfulRoutingAux_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:05:45.590674+00:00
-- url     : https://prove2.me/theorems/ea70c8de-afae-4fbe-988c-f7a77930dcd7
-- title:
--   HH18 Parameterized: decoded Retry Pool Protocol Path Successful Routing Aux succ
-- statement:
--   The HH18 Parameterized construction uses the decoded Retry Pool Protocol Path Successful Routing Aux succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Paths/SuccessEvent.lean#L61-L79
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Paths/SuccessEvent.lean#L61-L79

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Paths_NestedPathRouting
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_SelectedEnoughBranch
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Paths_SuccessEvent
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.FiniteInstrument
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolPathSuccessfulRoutingAux_succ
    (m w z q stage : Nat) (hstage : stage + 1 < z)
    (path : routedDepthOutputSlots m w (stage + 1))
    (outcome : decodedRetryPoolProtocolOutcomeAux m w z q (stage + 1) hstage) :
    decodedRetryPoolProtocolPathSuccessfulRoutingAux
        m w z q (stage + 1) hstage path outcome =
      (decodedRetryPoolProtocolPathSuccessfulRoutingAux
          m w z q stage (by omega)
            (routedDepthOutputPathInit m w stage path) outcome.1 &&
        decodedRetryPoolSuccessorStageSelectedPoolEnough
          m w z q ⟨stage, by omega⟩ hstage
            (routedDepthOutputPathLast m w stage path)
            (nestedTensorHistoryAt
              (decodedRetryPoolSuccessorStageOutcome
                m w z q ⟨stage, by omega⟩ hstage)
              (logicalOutputCount m w) stage outcome.2
              ((decodedRetryPoolNestedPathEquiv m w stage).symm
                (routedDepthOutputPathInit m w stage path)))) := by sorry

attribute [defeq] QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolPathSuccessfulRoutingAux_succ
