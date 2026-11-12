-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthErrorEnvelope_succ_le_quarter
-- name    : QEC.Distillation.HH18Parameterized.routedDepthErrorEnvelope_succ_le_quarter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:03:57.321228+00:00
-- url     : https://prove2.me/theorems/f315a32f-c1bc-4875-853f-003f08b5ac4b
-- title:
--   HH18 Parameterized: routed Depth Error Envelope succ le quarter
-- statement:
--   The global envelope contracts by a factor of four, uniformly over all
--   finite logical-port paths it bounds.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/PathEnvelope.lean#L925-L982
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/PathEnvelope.lean#L925-L982

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

theorem QEC.Distillation.HH18Parameterized.routedDepthErrorEnvelope_succ_le_quarter {w r m : Nat}
    (h : Admissible w r m) (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon) (depth : Nat) :
    routedDepthErrorEnvelope w r m epsilon (depth + 1) ≤
      routedDepthErrorEnvelope w r m epsilon depth / 4 := by sorry
