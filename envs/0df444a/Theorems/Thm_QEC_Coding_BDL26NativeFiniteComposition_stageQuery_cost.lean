-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_stageQuery_cost
-- name    : QEC.Coding.BDL26NativeFiniteComposition.stageQuery_cost
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T11:50:47.678991+00:00
-- url     : https://prove2.me/theorems/1c4cf828-9e0c-4334-b2cb-cacc170a6787
-- title:
--   BDL26 Native Finite Composition: stage Query cost
-- statement:
--   The BDL26 Native Finite Composition construction uses the stage Query cost property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeFiniteComposition.lean#L1671-L1678
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeFiniteComposition.lean#L1671-L1678

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

theorem QEC.Coding.BDL26NativeFiniteComposition.stageQuery_cost {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (J : StageMaps p n) (T : NativeTable (perturbationOddScale p) n) :
    (stageQuery p n (canonicalRows _ n J) T).2 =
      Paid.operationCost _ n (canonicalRows _ n J) (radius_nonneg p) p.lambda
        ((6*p.m+2)*p.lambda) T+(deterministicCost p n : ℝ≥0∞) := by sorry
