-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_source_even_geometry_cost
-- name    : QEC.Coding.BDL26NativeFiniteComposition.source_even_geometry_cost
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T12:32:51.641719+00:00
-- url     : https://prove2.me/theorems/5e3aaa1a-9777-46da-99aa-9bfb6e04b0ee
-- title:
--   BDL26 Native Finite Composition: source even geometry cost
-- statement:
--   The BDL26 Native Finite Composition construction uses the source even geometry cost property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeFiniteComposition.lean#L2517-L2524
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeFiniteComposition.lean#L2517-L2524

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

theorem QEC.Coding.BDL26NativeFiniteComposition.source_even_geometry_cost {L : ℝ} (p : GeometricParameters L) (k : ℕ) :
    (∫⁻ z,totalCost p (2*k) z ∂experimentLaw p (2*k)) ≤
      (totalCoefficient p*(stageQubits p (2*k)+1)^1774 : ℕ) ∧
    ∀ᵐ z ∂experimentLaw p (2*k),
      PhysicalGeometry (perturbationOddScale p) (2*k) (evaluate p (2*k) z) p.t := by sorry
