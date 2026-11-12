-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_Decoded_evaluate_zero
-- name    : QEC.Coding.BDL26NativeFiniteComposition.Decoded.evaluate_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T11:42:57.6457+00:00
-- url     : https://prove2.me/theorems/b6f25f4a-1ebd-46b4-b456-675145bc7856
-- title:
--   Decoded: evaluate zero
-- statement:
--   The Decoded construction uses the evaluate zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeFiniteComposition.lean#L2678-L2679
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeFiniteComposition.lean#L2678-L2679

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricJointExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeFiniteComposition
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_evaluate_zero
attribute [local simp] QEC.Coding.BDL26FiniteEmbeddingExperiment.evaluate_zero


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
open QEC.Coding.BDL26NativeFiniteComposition.Decoded

theorem QEC.Coding.BDL26NativeFiniteComposition.Decoded.evaluate_zero {L : ℝ} (p : GeometricParameters L) (z : Experiment p 0) :
    evaluate p 0 z = BDL26RandomSeedEmbedding.seedPoint (perturbationOddScale p) := by sorry

attribute [defeq] QEC.Coding.BDL26NativeFiniteComposition.Decoded.evaluate_zero
