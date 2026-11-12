-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeGeometricExecution_refresh_local_cost
-- name    : QEC.Coding.BDL26NativeGeometricExecution.refresh_local_cost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T10:06:12.746662+00:00
-- url     : https://prove2.me/theorems/b90db204-2213-4fe1-bbd6-7447f6234fe6
-- title:
--   BDL26 Native Geometric Execution: refresh local cost
-- statement:
--   Only the bounded cache refresh cost is claimed here, separately from all
--   paid eligibility/order/query work and its still-separate expectation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricExecution.lean#L223-L230
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricExecution.lean#L223-L230

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeKeyExecutionBridge
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricExecution
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26NativeGeometricExecution
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26BoundedValence
open BDL26ReplacementEmbedding BDL26TannerLocalRegularity
open BDL26RandomPerturbation BDL26KeyedGeometric BDL26KeyedGeometricExecution
open BDL26NativeKeyExecutionBridge
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
open scoped Classical BigOperators ENNReal

theorem QEC.Coding.BDL26NativeGeometricExecution.refresh_local_cost (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) (r : ℝ) (row : LiveRow S n J r)
    (T : NativeTable S n) (R : SR.Rows (SR.Index S n)) :
    (SR.refreshQ T (support S n J r row) R).operations ≤ 35*R.length ∧
    (SR.refreshQ T (support S n J r row) R).allocations ≤ 2*R.length := by sorry
