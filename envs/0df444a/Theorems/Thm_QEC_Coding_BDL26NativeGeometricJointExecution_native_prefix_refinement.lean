-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeGeometricJointExecution_native_prefix_refinement
-- name    : QEC.Coding.BDL26NativeGeometricJointExecution.native_prefix_refinement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T09:56:04.806448+00:00
-- url     : https://prove2.me/theorems/b8f564fd-1459-4255-b727-5e95335010d3
-- title:
--   BDL26 Native Geometric Joint Execution: native prefix refinement
-- statement:
--   Entire rows, every stable-code trace entry, and the precise numeric cost.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricJointExecution.lean#L495-L539
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricJointExecution.lean#L495-L539

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

theorem QEC.Coding.BDL26NativeGeometricJointExecution.native_prefix_refinement (S : OddScale) (n : ℕ) (J : Input S n)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ) (T : NativeTable S n) (m : ℕ) :
    (prefixQ S n J hr lambda K T m).value.rows =
      sampleRows S n T (countedPrefix S n J r lambda K T m).1 ∧
    (prefixQ S n J hr lambda K T m).value.trace.map (eraseChoice S n J r) =
      (countedPrefix S n J r lambda K T m).2.1 ∧
    (prefixQ S n J hr lambda K T m).operations =
      (countedPrefix S n J r lambda K T m).2.2 := by sorry
