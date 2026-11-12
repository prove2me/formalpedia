-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_Decoded_prefix_comp
-- name    : QEC.Coding.BDL26NativeFiniteComposition.Decoded.prefix_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T11:51:57.35727+00:00
-- url     : https://prove2.me/theorems/c9388963-e523-4dcc-8611-507df1ce6595
-- title:
--   Decoded: prefix comp
-- statement:
--   Prefix composition is a pointwise identity, without an almost-everywhere restriction.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeFiniteComposition.lean#L2633-L2650
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeFiniteComposition.lean#L2633-L2650

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricJointExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PaidRowsComposition
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeFiniteComposition
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_prefix_comp
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans

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

theorem QEC.Coding.BDL26NativeFiniteComposition.Decoded.prefix_comp {L : ℝ} (p : GeometricParameters L) {l m n : ℕ}
    (hlm : l ≤ m) (hmn : m ≤ n) (z : Experiment p n) :
    experimentPrefix p l m hlm (experimentPrefix p m n hmn z) = experimentPrefix p l n (hlm.trans hmn) z := by sorry
