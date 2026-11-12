-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthActualRun_root
-- name    : QEC.Distillation.HH18Parameterized.routedDepthActualRun_root
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:21:19.381033+00:00
-- url     : https://prove2.me/theorems/80381aab-1c6d-4005-b860-da6254e0d0f9
-- title:
--   HH18 Parameterized: routed Depth Actual Run root
-- statement:
--   The root of the recursively indexed construction is exactly the actual
--   one-level run at the original physical input rate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/FreshDepth.lean#L150-L156
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/FreshDepth.lean#L150-L156

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_DepthTwoRouting
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_FreshDepth
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

theorem QEC.Distillation.HH18Parameterized.routedDepthActualRun_root {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) :
    routedDepthActualRun h hdegree (RoutedDepthState.root (h := h)
      (hdegree := hdegree) (epsilon := epsilon)) =
      resourceDecodedRun h hdegree (noisyResources m w epsilon) := by sorry
