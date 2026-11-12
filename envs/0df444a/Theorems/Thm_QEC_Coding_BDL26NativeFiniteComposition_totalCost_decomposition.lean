-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_totalCost_decomposition
-- name    : QEC.Coding.BDL26NativeFiniteComposition.totalCost_decomposition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T12:41:22.915456+00:00
-- url     : https://prove2.me/theorems/bac67241-9741-4d66-9870-220e7b9a32fb
-- title:
--   BDL26 Native Finite Composition: total Cost decomposition
-- statement:
--   Exact decomposition of the actual recursion: unchanged native work,
--   additional first-match input reads, affine row transfer, replacement work.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeFiniteComposition.lean#L3101-L3114
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeFiniteComposition.lean#L3101-L3114

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

theorem QEC.Coding.BDL26NativeFiniteComposition.totalCost_decomposition {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (z : Experiment p N) : totalCost p N z =
    ∑ i : Fin N,
      (nativeOperationCost (perturbationOddScale p) i.val (stageInput p N i z)
        (radius_nonneg p) p.lambda ((6*p.m+2)*p.lambda) (tableAt p N i z)+
      Paid.additionalIncomingCost (perturbationOddScale p) i.val (inputRows p N i z)
        (radius_nonneg p) p.lambda ((6*p.m+2)*p.lambda) (tableAt p N i z)+
      (perturbLabelCost p i.val : ℝ≥0∞)+(materializationLabelCost p i.val : ℝ≥0∞)) := by sorry
