-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeKeyExecutionBridge_scan_actual
-- name    : QEC.Coding.BDL26NativeKeyExecutionBridge.scan_actual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T09:33:23.363575+00:00
-- url     : https://prove2.me/theorems/1dd6b632-27fa-4408-81b0-0f05f639aa88
-- title:
--   BDL26 Native Key Execution Bridge: scan actual
-- statement:
--   Selection follows the paid native order; no equality to legacy order is used.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeKeyExecutionBridge.lean#L703-L726
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeKeyExecutionBridge.lean#L703-L726

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeMasterCandidates
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricAvoidance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventUniverse
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeKeyExecutionBridge
import Theorems.Thm_QEC_Coding_BDL26NativeTriangleColors_nativeKey_injective
import Theorems.Thm_QEC_Coding_BDL26NativeTriangleColors_scan_actual

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26NativeKeyExecutionBridge
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26ReplacementEmbedding
open BDL26RandomPerturbation BDL26KeyedGeometric BDL26KeyedGeometricExecution
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
open scoped Classical BigOperators ENNReal

theorem QEC.Coding.BDL26NativeKeyExecutionBridge.scan_actual (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {r : ℝ} (hr : 0 ≤ r)
    (lambda : ℝ) (K : ℕ) (R : SR.Rows (SR.Index S n)) :
    (scanQ S n J hr lambda K R).1.map (event S n J r) =
      select (localEvent
        (keySupport (Presentation S n) (NC.nativeKey S n) (NC.nativeKey_injective S n) J r)
        (keyBad (Presentation S n) (NC.nativeKey S n) (NC.nativeKey_injective S n)
          J r lambda K)) (originalPoints S n R) := by sorry
