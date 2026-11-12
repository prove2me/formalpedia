-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthPathStageRate_le_errorEnvelope
-- name    : QEC.Distillation.HH18Parameterized.routedDepthPathStageRate_le_errorEnvelope
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:06:30.897202+00:00
-- url     : https://prove2.me/theorems/7f2481a4-3762-4cac-86bf-9090a1839209
-- title:
--   HH18 Parameterized: routed Depth Path Stage Rate le error Envelope
-- statement:
--   Every finite stage rate is bounded by the uniform envelope at that same
--   stage, while retaining its literal selected prefix.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/PathYield.lean#L157-L166
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/PathYield.lean#L157-L166

import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathEnvelope
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathYield
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.PauliSymplectic
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open scoped BigOperators
open Triorthogonal.BH12NoisyInjection
open Triorthogonal.BH12NoisyInjection.OneQubit
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.HH18Parameterized.routedDepthPathStageRate_le_errorEnvelope {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) (path : routedDepthOutputSlots m w depth) (stage : Fin depth) :
    (routedDepthPathRate h hdegree epsilon hsmall stage.1
      (routedDepthPathStagePath m w depth path stage)).1 ≤
        routedDepthErrorEnvelope w r m epsilon stage.1 := by sorry
