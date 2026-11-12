-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_Paid_prefix_refinement
-- name    : QEC.Coding.BDL26NativeFiniteComposition.Paid.prefix_refinement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T11:47:58.527339+00:00
-- url     : https://prove2.me/theorems/1ef2bce2-1fd5-4612-adfa-9721acbf0534
-- title:
--   Paid: prefix refinement
-- statement:
--   Same native row state and same stable code trace, including bad inputs.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeFiniteComposition.lean#L992-L1030
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeFiniteComposition.lean#L992-L1030

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricJointExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeFiniteComposition
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26NativeFiniteComposition
open Classical MeasureTheory ProbabilityTheory
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26BoundedValence
open BDL26DecodingGraph
open BDL26ReplacementEmbedding BDL26TannerLocalRegularity BDL26RandomPerturbation
open BDL26KeyedGeometric BDL26KeyedGeometricExecution BDL26NativeKeyExecutionBridge
open BDL26NativeGeometricExecution BDL26NativeGeometricExecutionCost
open BDL26NativeGeometricScanCost BDL26NativeGeometricJointExecution
open BDL26ReplacementMaterialization BDL26FiniteEmbeddingExperiment
open BDL26RandomPhysicalLocality
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open scoped ENNReal BigOperators
attribute [local instance] QEC.Coding.BDL26NativeFiniteComposition.labelListMeasurable
attribute [local instance] QEC.Coding.BDL26NativeFiniteComposition.labelListSingleton
attribute [local instance] QEC.Coding.BDL26NativeFiniteComposition.labelListMeasurable QEC.Coding.BDL26NativeFiniteComposition.labelListSingleton
open QEC.Coding.BDL26NativeFiniteComposition.Paid

theorem QEC.Coding.BDL26NativeFiniteComposition.Paid.prefix_refinement (S : OddScale) (n : ℕ) (I : Rows S n)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ) (T : NativeTable S n) (m : ℕ) :
    (prefixQ S n I r lambda K T m).value.1 =
      (BDL26NativeGeometricExecution.prefixQ S n (rowMap S n I) hr lambda K T m).value.rows ∧
    (prefixQ S n I r lambda K T m).value.2 =
      (BDL26NativeGeometricExecution.prefixQ S n (rowMap S n I) hr lambda K T m).value.trace.map
        (eraseChoice S n (rowMap S n I) r) ∧
    (prefixQ S n I r lambda K T m).operations ≤ multiplier I*
      (BDL26NativeGeometricExecution.prefixQ S n (rowMap S n I) hr lambda K T m).operations := by sorry
