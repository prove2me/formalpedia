-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthPathStageRun_successProbability_eq_decodedInstrument_bornWeight
-- name    : QEC.Distillation.HH18Parameterized.routedDepthPathStageRun_successProbability_eq_decodedInstrument_bornWeight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:12:22.164342+00:00
-- url     : https://prove2.me/theorems/b74663c7-8ca4-40ed-9649-11f5de514c9d
-- title:
--   HH18 Parameterized: routed Depth Path Stage Run success Probability eq decoded Instrument born Weight
-- statement:
--   Every routed-stage success probability is exactly the accepted Born
--   weight of the decoded finite instrument used by each physical retry pool.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/ScheduleBridge.lean#L187-L204
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/ScheduleBridge.lean#L187-L204

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_Accounting
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_RecordRouting
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Schedule
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_ScheduleBridge
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

theorem QEC.Distillation.HH18Parameterized.routedDepthPathStageRun_successProbability_eq_decodedInstrument_bornWeight
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) (path : routedDepthOutputSlots m w depth) (stage : Fin depth) :
    (routedDepthPathStageRun h hdegree epsilon hsmall depth path stage).successProbability =
      (decodedInstrument h hdegree).bornWeight .accepted
        (prepareMeasuredResources m w
          (noisyResources m w
            (routedDepthPathRate h hdegree epsilon hsmall stage.1
              (routedDepthPathStagePath m w depth path stage)))) := by sorry
