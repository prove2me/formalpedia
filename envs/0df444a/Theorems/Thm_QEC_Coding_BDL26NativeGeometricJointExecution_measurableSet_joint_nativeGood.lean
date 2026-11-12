-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeGeometricJointExecution_measurableSet_joint_nativeGood
-- name    : QEC.Coding.BDL26NativeGeometricJointExecution.measurableSet_joint_nativeGood
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T09:57:29.790715+00:00
-- url     : https://prove2.me/theorems/a5abe8df-267a-4274-88f3-60d615e8b9a1
-- title:
--   BDL26 Native Geometric Joint Execution: measurable Set joint native Good
-- statement:
--   The exact original support-and-avoidance event is jointly Borel. This is
--   the measurable event used below, before its deterministic geometry handoff.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricJointExecution.lean#L992-L1007
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricJointExecution.lean#L992-L1007

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

theorem QEC.Coding.BDL26NativeGeometricJointExecution.measurableSet_joint_nativeGood (S : OddScale) (n : ℕ)
    {L : ℝ} (p : GeometricParameters L) :
    MeasurableSet {y : Input S n × Input S n |
      y.2 ∈ BDL26NativeGeometricAvoidance.NativeGood S n y.1 p} := by sorry
