-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthPathYieldFactor_eq_decodedInstrument_bornWeight_product
-- name    : QEC.Distillation.HH18Parameterized.routedDepthPathYieldFactor_eq_decodedInstrument_bornWeight_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:17:46.83341+00:00
-- url     : https://prove2.me/theorems/1c00ff31-05df-4366-9860-415d888bd427
-- title:
--   HH18 Parameterized: routed Depth Path Yield Factor eq decoded Instrument born Weight product
-- statement:
--   A path yield is literally the product of accepted decoded-instrument Born
--   weights along that physical routed path.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/ScheduleBridge.lean#L208-L224
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/RetryPool/Physical/ScheduleBridge.lean#L208-L224

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

theorem QEC.Distillation.HH18Parameterized.routedDepthPathYieldFactor_eq_decodedInstrument_bornWeight_product
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) (path : routedDepthOutputSlots m w depth) :
    (routedDepthPathYieldFactor h hdegree epsilon hsmall depth path : ℝ) =
      ∏ stage : Fin depth,
        (decodedInstrument h hdegree).bornWeight .accepted
          (prepareMeasuredResources m w
            (noisyResources m w
              (routedDepthPathRate h hdegree epsilon hsmall stage.1
                (routedDepthPathStagePath m w depth path stage)))) := by sorry
