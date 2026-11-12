-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_two_mul_routedDepthPhysicalInputCount_le_iterationScale
-- name    : QEC.Distillation.HH18Parameterized.two_mul_routedDepthPhysicalInputCount_le_iterationScale
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:36:20.659759+00:00
-- url     : https://prove2.me/theorems/09ddf71b-3f7e-49cc-a3d4-134179ca989e
-- title:
--   HH18 Parameterized: two mul routed Depth Physical Input Count le iteration Scale
-- statement:
--   The scale retains a visible multiple of the actual block input count for
--   later uniform pooled-resource accounting.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/PathEnvelope.lean#L71-L75
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/PathEnvelope.lean#L71-L75

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

theorem QEC.Distillation.HH18Parameterized.two_mul_routedDepthPhysicalInputCount_le_iterationScale (w r m : Nat) :
    2 * (physicalInputCount m w : ℝ) ≤ routedDepthIterationScale w r m := by sorry
