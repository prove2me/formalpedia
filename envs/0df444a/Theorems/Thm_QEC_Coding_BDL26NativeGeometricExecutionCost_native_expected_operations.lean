-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeGeometricExecutionCost_native_expected_operations
-- name    : QEC.Coding.BDL26NativeGeometricExecutionCost.native_expected_operations
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T09:51:07.563372+00:00
-- url     : https://prove2.me/theorems/21961ba0-c1e6-494a-8e36-6d20cbe8bccd
-- title:
--   BDL26 Native Geometric Execution Cost: native expected operations
-- statement:
--   Expected TOTAL paid operations for the unchanged native master-row process.
--   Halting, product law, first and strict second moments are all derived internally.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricExecutionCost.lean#L861-L909
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricExecutionCost.lean#L861-L909

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricScanCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedCostMeasurability
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExpectedOperationCost
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_StrictSlackMoments
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricExecutionCost
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26NativeGeometricExecutionCost
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26BoundedValence
open BDL26ReplacementEmbedding BDL26TannerLocalRegularity
open BDL26RandomPerturbation BDL26KeyedGeometric BDL26KeyedGeometricExecution
open BDL26NativeKeyExecutionBridge BDL26NativeGeometricExecution
open BDL26NativeGeometricScanCost
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
open scoped Classical BigOperators ENNReal

theorem QEC.Coding.BDL26NativeGeometricExecutionCost.native_expected_operations (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {L : ℝ} (p : GeometricParameters L)
    (hJ : IsBoundedDensityLocalMap (Presentation S n) J p.t) :
    (∫⁻ T, nativeOperationCost S n J (radius_nonneg p) p.lambda
      ((6*p.m+2)*p.lambda) T ∂nativeTableMeasure S n p) ≤
        (expectedOperationBudget S n ((6*p.m+2)*p.lambda) (dependencyBound p.M) : ℕ) := by sorry
