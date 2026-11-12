-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeGeometricJointExecution_measurable_joint_nativeOperationCost
-- name    : QEC.Coding.BDL26NativeGeometricJointExecution.measurable_joint_nativeOperationCost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T09:56:59.531214+00:00
-- url     : https://prove2.me/theorems/3251b09d-0c4d-4ca8-8643-b29a79bf6007
-- title:
--   BDL26 Native Geometric Joint Execution: measurable joint native Operation Cost
-- statement:
--   Joint measurability includes every actual arithmetic branch cost and infinity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricJointExecution.lean#L809-L838
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricJointExecution.lean#L809-L838

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

theorem QEC.Coding.BDL26NativeGeometricJointExecution.measurable_joint_nativeOperationCost (S : OddScale) (n : ℕ)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ) :
    Measurable (fun z : JointInput S n => nativeOperationCost S n z.1 hr lambda K z.2) := by sorry
