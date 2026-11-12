-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeGeometricJointExecution_native_random_input_total_cost
-- name    : QEC.Coding.BDL26NativeGeometricJointExecution.native_random_input_total_cost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T10:00:53.06191+00:00
-- url     : https://prove2.me/theorems/24c69ba8-1930-4d68-8790-7a8b759d7b4d
-- title:
--   BDL26 Native Geometric Joint Execution: native random input total cost
-- statement:
--   The SAME coefficient depends only on jointly fixed p; exponent 1772 and
--   the actual entire paid process are unchanged for every S,n and input law ν.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricJointExecution.lean#L1117-L1135
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricJointExecution.lean#L1117-L1135

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricExecutionCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedCostMeasurability
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GoodMapMeasurability
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricJointExecution
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26NativeGeometricJointExecution
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26BoundedValence
open BDL26ReplacementEmbedding BDL26TannerLocalRegularity
open BDL26RandomPerturbation BDL26KeyedGeometric BDL26KeyedGeometricExecution
open BDL26NativeKeyExecutionBridge BDL26NativeGeometricExecution
open BDL26NativeGeometricScanCost BDL26NativeGeometricExecutionCost
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
open scoped Classical BigOperators ENNReal
attribute [local instance] QEC.Coding.BDL26NativeGeometricJointExecution.labelListMeasurable
attribute [local instance] QEC.Coding.BDL26NativeGeometricJointExecution.labelListSingleton
attribute [local instance] QEC.Coding.BDL26NativeGeometricJointExecution.labelListMeasurable QEC.Coding.BDL26NativeGeometricJointExecution.labelListSingleton

theorem QEC.Coding.BDL26NativeGeometricJointExecution.native_random_input_total_cost (S : OddScale) (n : ℕ) {L : ℝ}
    (p : GeometricParameters L) (ν : Measure (Input S n)) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ J ∂ν, IsBoundedDensityLocalMap (Presentation S n) J p.t) :
    (∫⁻ z, nativeOperationCost S n z.1 (radius_nonneg p) p.lambda
      ((6*p.m+2)*p.lambda) z.2 ∂ν.prod (nativeTableMeasure S n p)) ≤
      (nativeOperationCoefficient ((6*p.m+2)*p.lambda) (dependencyBound p.M)*
        (Fintype.card (Presentation S n).Q+1)^nativeOperationDegree : ℕ) := by sorry
