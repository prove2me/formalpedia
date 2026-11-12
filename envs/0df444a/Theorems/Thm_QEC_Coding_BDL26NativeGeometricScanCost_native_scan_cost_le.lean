-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeGeometricScanCost_native_scan_cost_le
-- name    : QEC.Coding.BDL26NativeGeometricScanCost.native_scan_cost_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T09:36:30.579482+00:00
-- url     : https://prove2.me/theorems/e17aae17-61df-44b1-b76b-0aa25a8a159a
-- title:
--   BDL26 Native Geometric Scan Cost: native scan cost le
-- statement:
--   A derived bound on the ACTUAL paid native scan, including all generated
--   master rows before filtering, actual native sorting and repeated query setup.
--   No law, trace, cost certificate, legacy order or halting premise is an input.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricScanCost.lean#L313-L326
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricScanCost.lean#L313-L326

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeKeyExecutionBridge
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExpectedOperationCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricScanCost
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26NativeGeometricScanCost
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open BDL26NativeKeyExecutionBridge
open scoped Classical

theorem QEC.Coding.BDL26NativeGeometricScanCost.native_scan_cost_le (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {r : ℝ} (hr : 0 ≤ r)
    (lambda : ℝ) (K : ℕ) (R : SR.Rows (SR.Index S n)) :
    (scanQ S n J hr lambda K R).2 ≤ scanBudget S n K R.length := by sorry
