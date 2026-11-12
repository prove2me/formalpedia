-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_finiteSuccess_handoff
-- name    : QEC.Coding.BDL26NativeFiniteComposition.finiteSuccess_handoff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T12:32:32.216315+00:00
-- url     : https://prove2.me/theorems/ee51a36c-2ef3-4e29-969c-6d3ac2a1ee26
-- title:
--   BDL26 Native Finite Composition: finite Success handoff
-- statement:
--   Original NativeGood yields the original incoming-face and labelled-triangle
--   handoff, on the same full history and the same native table.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeFiniteComposition.lean#L2299-L2310
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeFiniteComposition.lean#L2299-L2310

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

theorem QEC.Coding.BDL26NativeFiniteComposition.finiteSuccess_handoff {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    {z : Experiment p N} (hz : z ∈ finiteSuccess p N) (i : Fin N) :
    IncomingFaceGeometry (StagePresentation p i.val) (perturbationOddScale p)
      (nativePerturbed p i.val (stageInput p N i z) (tableAt p N i z))
      (((p.m : ℝ)-1)*p.lambda) ((6*(p.m : ℝ)*widthFactor-1)*p.lambda) ∧
    ∀ center, ((familyHits (oldTriangleImage (StagePresentation p i.val)
      (nativePerturbed p i.val (stageInput p N i z) (tableAt p N i z)))
      (Metric.closedBall center 1)).card : ℝ) ≤ triangleDensityBound := by sorry
