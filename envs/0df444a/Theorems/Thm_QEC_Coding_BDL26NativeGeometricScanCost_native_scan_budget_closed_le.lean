-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeGeometricScanCost_native_scan_budget_closed_le
-- name    : QEC.Coding.BDL26NativeGeometricScanCost.native_scan_budget_closed_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T09:50:53.450203+00:00
-- url     : https://prove2.me/theorems/bb042fa7-71a0-47d0-934b-3529a2997d57
-- title:
--   BDL26 Native Geometric Scan Cost: native scan budget closed le
-- statement:
--   Every retained scalar component is replaced by its syntax-derived polynomial.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricScanCost.lean#L344-L389
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricScanCost.lean#L344-L389

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

theorem QEC.Coding.BDL26NativeGeometricScanCost.native_scan_budget_closed_le (S : OddScale) (n K z : ℕ) :
    let a := (n+1)*(BDL26NativePresentationGenerator.inputRadius S n)^220
    let b := (n+1)*(BDL26NativePresentationGenerator.inputRadius S n)^15
    scanBudget S n K z ≤ closedScanBudget a b K z := by sorry
