-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthErrorEnvelope_scaled_small
-- name    : QEC.Distillation.HH18Parameterized.routedDepthErrorEnvelope_scaled_small
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:03:18.981746+00:00
-- url     : https://prove2.me/theorems/40bda489-1821-4d0b-9d80-0e1d507d0be0
-- title:
--   HH18 Parameterized: routed Depth Error Envelope scaled small
-- statement:
--   The uniform envelope itself remains in the scaled quarter-domain at every
--   finite depth.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/PathEnvelope.lean#L904-L921
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/PathEnvelope.lean#L904-L921

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

theorem QEC.Distillation.HH18Parameterized.routedDepthErrorEnvelope_scaled_small {w r m : Nat}
    (h : Admissible w r m) (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon) (depth : Nat) :
    routedDepthIterationScale w r m *
      routedDepthErrorEnvelope w r m epsilon depth ≤ 1 / 4 := by sorry
