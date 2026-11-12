-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthPathRate_le_errorEnvelope
-- name    : QEC.Distillation.HH18Parameterized.routedDepthPathRate_le_errorEnvelope
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:35:41.551855+00:00
-- url     : https://prove2.me/theorems/313ee271-fcda-443a-8b8b-675af02a55fd
-- title:
--   HH18 Parameterized: routed Depth Path Rate le error Envelope
-- statement:
--   The actual selector rate on every finite path is bounded by the separate
--   uniform distance-power envelope.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/PathEnvelope.lean#L660-L701
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/PathEnvelope.lean#L660-L701

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_FreshDepth
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathEnvelope
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

theorem QEC.Distillation.HH18Parameterized.routedDepthPathRate_le_errorEnvelope {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon) :
    ∀ (depth : Nat) (path : routedDepthOutputSlots m w depth),
      (routedDepthPathRate h hdegree epsilon hsmall depth path).1 ≤
        routedDepthErrorEnvelope w r m epsilon depth := by sorry
