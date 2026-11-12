-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_fixed_parameters_all_finite
-- name    : QEC.Coding.BDL26NativeFiniteComposition.fixed_parameters_all_finite
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T12:03:10.686678+00:00
-- url     : https://prove2.me/theorems/4a6c1633-7ddf-4e8a-89c7-197d6f26d24e
-- title:
--   BDL26 Native Finite Composition: fixed parameters all finite
-- statement:
--   The BDL26 Native Finite Composition construction uses the fixed parameters all finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeFiniteComposition.lean#L2503-L2515
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeFiniteComposition.lean#L2503-L2515

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

theorem QEC.Coding.BDL26NativeFiniteComposition.fixed_parameters_all_finite (L : ℝ) :
    ∃ p : GeometricParameters L, ∀ N : ℕ,
      Measurable (history p N) ∧ Measurable (totalCost p N) ∧
      (∫⁻ z,totalCost p N z ∂experimentLaw p N) ≤
        (totalCoefficient p*(stageQubits p N+1)^1774 : ℕ) ∧
      Integrable (fun z => (totalCost p N z).toReal) (experimentLaw p N) ∧
      ∀ᵐ z ∂experimentLaw p N, z ∈ finiteSuccess p N ∧ totalCost p N z<∞ ∧
        ∀ i : Fin (N+1), PhysicalGeometry (perturbationOddScale p) i.val (history p N z i) p.t := by sorry
