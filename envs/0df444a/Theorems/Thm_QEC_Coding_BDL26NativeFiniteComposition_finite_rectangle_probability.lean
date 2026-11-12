-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_finite_rectangle_probability
-- name    : QEC.Coding.BDL26NativeFiniteComposition.finite_rectangle_probability
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T11:59:28.345197+00:00
-- url     : https://prove2.me/theorems/28e46b35-5d7e-40a6-ac8a-de96f6070499
-- title:
--   BDL26 Native Finite Composition: finite rectangle probability
-- statement:
--   Every selected finite rectangle factors; unused factors remain the original whole laws.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeFiniteComposition.lean#L1999-L2027
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeFiniteComposition.lean#L1999-L2027

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricJointExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeFiniteComposition
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_finite_rectangle_probability

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

theorem QEC.Coding.BDL26NativeFiniteComposition.finite_rectangle_probability {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (A : Finset (Fin n)) (B : (i : Fin n) → Set (StageTables p i.val)) :
    experimentLaw p n (⋂ i ∈ A, tableAt p n i ⁻¹' B i) =
      ∏ i ∈ A, freshLaw p i.val (B i) := by sorry
