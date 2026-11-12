-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_Decoded_full_rectangle_succ
-- name    : QEC.Coding.BDL26NativeFiniteComposition.Decoded.full_rectangle_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T12:19:26.259598+00:00
-- url     : https://prove2.me/theorems/854299d0-985d-4d7f-a7cc-36941d08be59
-- title:
--   Decoded: full rectangle succ
-- statement:
--   The full dependent rectangle splits into the preceding rectangle and final table set.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeFiniteComposition.lean#L2836-L2849
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeFiniteComposition.lean#L2836-L2849

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricJointExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeFiniteComposition
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_full_rectangle_succ

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

theorem QEC.Coding.BDL26NativeFiniteComposition.Decoded.full_rectangle_succ {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (B : (i : Fin (n+1)) → Set (StageTables p i.val)) :
    {z : Experiment p (n+1) | ∀ i, tableAt p (n+1) i z ∈ B i} =
      {z : Experiment p n | ∀ i : Fin n, tableAt p n i z ∈ B i.castSucc} ×ˢ
        B (Fin.last n) := by sorry
