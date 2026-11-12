-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_full_paid_observation_decode_law
-- name    : QEC.Coding.BDL26NativeFiniteComposition.full_paid_observation_decode_law
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T12:40:51.277247+00:00
-- url     : https://prove2.me/theorems/ba33779b-7d10-4169-bece-4d4373191a60
-- title:
--   BDL26 Native Finite Composition: full paid observation decode law
-- statement:
--   Whole product and every paid observation travel together through the
--   proved inverse relabeling. The decoded mathematical recursion is separately
--   identified by evaluate_decoded/history_decoded, using the identical key.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeFiniteComposition.lean#L3239-L3253
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeFiniteComposition.lean#L3239-L3253

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

theorem QEC.Coding.BDL26NativeFiniteComposition.full_paid_observation_decode_law {L : ℝ} (p : GeometricParameters L) (N : ℕ) :
    (experimentLaw p N).map (fun z => (decodeExperiment p N z,observation p N z)) =
      (Decoded.experimentLaw p N).map
        (fun z => (z,observation p N (encodeExperiment p N z))) := by sorry
