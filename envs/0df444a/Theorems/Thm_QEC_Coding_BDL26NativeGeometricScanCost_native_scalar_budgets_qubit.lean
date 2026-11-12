-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeGeometricScanCost_native_scalar_budgets_qubit
-- name    : QEC.Coding.BDL26NativeGeometricScanCost.native_scalar_budgets_qubit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T09:51:18.071069+00:00
-- url     : https://prove2.me/theorems/4857e215-8bb3-406a-9e32-45b340501f69
-- title:
--   BDL26 Native Geometric Scan Cost: native scalar budgets qubit
-- statement:
--   All actual scalar budgets are now bounded solely in the actual native qubit
--   count. No retained generator cost or scale/depth coefficient survives.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricScanCost.lean#L706-L722
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricScanCost.lean#L706-L722

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

theorem QEC.Coding.BDL26NativeGeometricScanCost.native_scalar_budgets_qubit (S : OddScale) (n K : ℕ) :
    incomingBudget S n ≤ 19*(qubitRadius S n)^2 ∧
    scanBudget S n K (SR.count S n) ≤ scanPolynomialConstant K*(qubitRadius S n)^8 ∧
    SR.count S n ≤ qubitRadius S n := by sorry
