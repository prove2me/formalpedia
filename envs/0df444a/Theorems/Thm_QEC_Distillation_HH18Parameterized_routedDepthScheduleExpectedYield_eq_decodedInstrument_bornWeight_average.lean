-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthScheduleExpectedYield_eq_decodedInstrument_bornWeight_average
-- name    : QEC.Distillation.HH18Parameterized.routedDepthScheduleExpectedYield_eq_decodedInstrument_bornWeight_average
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:56:33.916198+00:00
-- url     : https://prove2.me/theorems/1f71a347-4a37-4a43-bfa3-912f66f686da
-- title:
--   HH18 Parameterized: routed Depth Schedule Expected Yield eq decoded Instrument born Weight average
-- statement:
--   The schedule yield is the normalized finite sum of physical accepted Born
--   weight products, one for every actual routed logical output path.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/ScheduleBridge.lean#L228-L248
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/ScheduleBridge.lean#L228-L248

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

theorem QEC.Distillation.HH18Parameterized.routedDepthScheduleExpectedYield_eq_decodedInstrument_bornWeight_average
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) :
    (routedDepthScheduleExpectedYield h hdegree epsilon hsmall depth : ℝ) =
      (∑ path : routedDepthOutputSlots m w depth,
        ∏ stage : Fin depth,
          (decodedInstrument h hdegree).bornWeight .accepted
            (prepareMeasuredResources m w
              (noisyResources m w
                (routedDepthPathRate h hdegree epsilon hsmall stage.1
                  (routedDepthPathStagePath m w depth path stage))))) /
        Fintype.card (routedDepthOutputSlots m w depth) := by sorry
