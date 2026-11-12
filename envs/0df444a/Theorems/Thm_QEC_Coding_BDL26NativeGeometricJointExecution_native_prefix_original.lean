-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeGeometricJointExecution_native_prefix_original
-- name    : QEC.Coding.BDL26NativeGeometricJointExecution.native_prefix_original
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T09:59:47.188653+00:00
-- url     : https://prove2.me/theorems/35136225-8bd3-4927-b80b-90977f2c88fc
-- title:
--   BDL26 Native Geometric Joint Execution: native prefix original
-- statement:
--   Stable codes preserve the entire original selection/trace, not only a
--   selected coordinate; all original counters and assignments are retained.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricJointExecution.lean#L723-L745
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricJointExecution.lean#L723-L745

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

theorem QEC.Coding.BDL26NativeGeometricJointExecution.native_prefix_original (S : OddScale) (n : ℕ) (J : Input S n)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ)
    (T : OriginalTable S n) (m : ℕ) :
    codedChoice S n J hr lambda K (SR.encodeSamples S n T) m =
      (selected (X := fun _ : Vertex (Presentation S n) => Space)
        (U S n J r) (B S n J r lambda K) T m).map (originalCode S n J r) ∧
    (prefixQ S n J hr lambda K (SR.encodeSamples S n T) m).value.trace.map
        (eraseChoice S n J r) =
      (originalTrace S n J r lambda K T m).map (Option.map (originalCode S n J r)) ∧
    (prefixQ S n J hr lambda K (SR.encodeSamples S n T) m).value.rows =
      sampleRows S n (SR.encodeSamples S n T)
        (fun a => counters (X := fun _ : Vertex (Presentation S n) => Space)
          (U S n J r) (B S n J r lambda K) T m (SR.decode S n a)) := by sorry
