-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthPhysicalInputCount_mul_envelope_sum_le_one_sixth
-- name    : QEC.Distillation.HH18Parameterized.routedDepthPhysicalInputCount_mul_envelope_sum_le_one_sixth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:04:11.85279+00:00
-- url     : https://prove2.me/theorems/95bdc34e-1db9-40cb-aadc-0bbd9ce562b3
-- title:
--   HH18 Parameterized: routed Depth Physical Input Count mul envelope sum le one sixth
-- statement:
--   The scale's visible block-size term turns the uniform envelope tail into
--   a finite physical-input budget required by later pooled-resource accounting.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/PathEnvelope.lean#L1021-L1046
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/PathEnvelope.lean#L1021-L1046

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

theorem QEC.Distillation.HH18Parameterized.routedDepthPhysicalInputCount_mul_envelope_sum_le_one_sixth
    {w r m : Nat} (h : Admissible w r m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon) (depth : Nat) :
    (physicalInputCount m w : ℝ) *
      (∑ stage : Fin depth, routedDepthErrorEnvelope w r m epsilon stage.1) ≤
        1 / 6 := by sorry
