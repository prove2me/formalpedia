-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_stage_nontermination_default
-- name    : QEC.Coding.BDL26NativeFiniteComposition.stage_nontermination_default
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T12:44:08.74391+00:00
-- url     : https://prove2.me/theorems/314e8181-15bb-44af-8b08-1a2a4bb48541
-- title:
--   BDL26 Native Finite Composition: stage nontermination default
-- statement:
--   Exceptional values and infinite costs refer to the very same stage table.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeFiniteComposition.lean#L3204-L3213
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeFiniteComposition.lean#L3204-L3213

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricJointExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeFiniteComposition
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

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

theorem QEC.Coding.BDL26NativeFiniteComposition.stage_nontermination_default {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (i : Fin N) (z : Experiment p N) (h : ¬stageHalts p N i z) :
    stageCost p N i z=∞ ∧
    nativeHaltTime (perturbationOddScale p) i.val (stageInput p N i z)
      (radius_nonneg p) p.lambda ((6*p.m+2)*p.lambda) (tableAt p N i z)=0 ∧
    nativeOutput (perturbationOddScale p) i.val (stageInput p N i z) p (tableAt p N i z)=
      (fun v => (tableAt p N i z) ((SR.decode (perturbationOddScale p) i.val).symm v,0)) := by sorry
