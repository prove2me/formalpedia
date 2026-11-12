-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolProtocolInstrumentAux_bornWeight_prefix_succ_sum
-- name    : QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolInstrumentAux_bornWeight_prefix_succ_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:25:51.125429+00:00
-- url     : https://prove2.me/theorems/20668007-88a7-44e0-a1e4-207dc8f88cfe
-- title:
--   HH18 Parameterized: decoded Retry Pool Protocol Instrument Aux born Weight prefix succ sum
-- statement:
--   Summing all actual observations of the next complete physical stage
--   recovers exactly the Born mass of the supplied predecessor history.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/BornMass.lean#L29-L57
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/BornMass.lean#L29-L57

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_SuccessEvent
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_SuccessBudget
import Definitions.Def_QEC_Semantics_Instruments_Sequential_BornMass
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_BornMass
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.FiniteInstrument
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.HH18Parameterized.decodedRetryPoolProtocolInstrumentAux_bornWeight_prefix_succ_sum
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (z q : Nat) (hz : 0 < z) (stage : Nat) (hstage : stage + 1 < z)
    (rho : DensityOperator (decodedRetryPoolProtocolRootInputCarrier m w z q hz))
    (outcome : decodedRetryPoolProtocolOutcomeAux m w z q stage (by omega)) :
    (∑ nextOutcome : nestedTensorHistory
        (decodedRetryPoolSuccessorStageOutcome
          m w z q ⟨stage, by omega⟩ hstage)
        (logicalOutputCount m w) stage,
      (decodedRetryPoolProtocolInstrumentAux
        h hdegree z q hz (stage + 1) hstage).bornWeight
          ⟨outcome, nextOutcome⟩ rho) =
      (decodedRetryPoolProtocolInstrumentAux
        h hdegree z q hz stage (by omega)).bornWeight outcome rho := by sorry
