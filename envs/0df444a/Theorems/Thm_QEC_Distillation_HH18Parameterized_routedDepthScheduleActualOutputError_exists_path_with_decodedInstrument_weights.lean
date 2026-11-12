-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthScheduleActualOutputError_exists_path_with_decodedInstrument_weights
-- name    : QEC.Distillation.HH18Parameterized.routedDepthScheduleActualOutputError_exists_path_with_decodedInstrument_weights
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:56:35.708339+00:00
-- url     : https://prove2.me/theorems/be2f197b-3762-412c-a235-db0cf2312619
-- title:
--   HH18 Parameterized: routed Depth Schedule Actual Output Error exists path with decoded Instrument weights
-- statement:
--   The reached finite error maximum is attained on a physical routed path,
--   and every stage of that same path exposes its decoded-instrument Born weight.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/ScheduleBridge.lean#L252-L272
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/ScheduleBridge.lean#L252-L272

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

theorem QEC.Distillation.HH18Parameterized.routedDepthScheduleActualOutputError_exists_path_with_decodedInstrument_weights
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) :
    ∃ path : routedDepthOutputSlots m w depth,
      routedDepthScheduleActualOutputError h hdegree epsilon hsmall depth =
          (routedDepthPathRate h hdegree epsilon hsmall depth path).1 ∧
        ∀ stage : Fin depth,
          (routedDepthPathStageRun h hdegree epsilon hsmall depth path stage).successProbability =
            (decodedInstrument h hdegree).bornWeight .accepted
              (prepareMeasuredResources m w
                (noisyResources m w
                  (routedDepthPathRate h hdegree epsilon hsmall stage.1
                    (routedDepthPathStagePath m w depth path stage)))) := by sorry
