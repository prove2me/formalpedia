-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeGeometricJointExecution_native_random_input_cost_integral
-- name    : QEC.Coding.BDL26NativeGeometricJointExecution.native_random_input_cost_integral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T10:01:41.55522+00:00
-- url     : https://prove2.me/theorems/3586cc66-ac28-4fae-9f8a-86bfb1beeca3
-- title:
--   BDL26 Native Geometric Joint Execution: native random input cost integral
-- statement:
--   Tonelli is applied to the genuine jointly measurable actual native cost.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricJointExecution.lean#L1099-L1106
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricJointExecution.lean#L1099-L1106

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

theorem QEC.Coding.BDL26NativeGeometricJointExecution.native_random_input_cost_integral (S : OddScale) (n : ℕ) {L : ℝ}
    (p : GeometricParameters L) (ν : Measure (Input S n)) [IsProbabilityMeasure ν] :
    (∫⁻ z, nativeOperationCost S n z.1 (radius_nonneg p) p.lambda
      ((6*p.m+2)*p.lambda) z.2 ∂ν.prod (nativeTableMeasure S n p)) =
      ∫⁻ J, ∫⁻ T, nativeOperationCost S n J (radius_nonneg p) p.lambda
        ((6*p.m+2)*p.lambda) T ∂nativeTableMeasure S n p ∂ν := by sorry
