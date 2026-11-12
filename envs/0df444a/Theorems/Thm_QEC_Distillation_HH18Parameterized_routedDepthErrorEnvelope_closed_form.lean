-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthErrorEnvelope_closed_form
-- name    : QEC.Distillation.HH18Parameterized.routedDepthErrorEnvelope_closed_form
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:35:52.886958+00:00
-- url     : https://prove2.me/theorems/08631605-5e40-4503-93a1-8f7d82510579
-- title:
--   HH18 Parameterized: routed Depth Error Envelope closed form
-- statement:
--   The derived envelope has the exact distance-power closed form.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/PathEnvelope.lean#L164-L197
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/PathEnvelope.lean#L164-L197

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

theorem QEC.Distillation.HH18Parameterized.routedDepthErrorEnvelope_closed_form {w r m : Nat}
    (h : Admissible w r m) (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (depth : Nat) :
    routedDepthIterationScale w r m * routedDepthErrorEnvelope w r m epsilon depth =
      (routedDepthIterationScale w r m * epsilon.1) ^ (codeDistance r w ^ depth) := by sorry
