-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_retained_history
-- name    : QEC.Coding.BDL26NativeFiniteComposition.retained_history
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T12:43:58.11536+00:00
-- url     : https://prove2.me/theorems/4d6938ba-20bb-4b54-8e8b-2d5b3b16bb65
-- title:
--   BDL26 Native Finite Composition: retained history
-- statement:
--   All actually retained incoming and returned rows are the complete canonical
--   label/payload list of the measured full history, with no missing assignment.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeFiniteComposition.lean#L3194-L3201
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeFiniteComposition.lean#L3194-L3201

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

theorem QEC.Coding.BDL26NativeFiniteComposition.retained_history {L : ℝ} (p : GeometricParameters L) (N : ℕ) (z : Experiment p N)
    (i : Fin (N+1)) :
    (run p i.val (experimentPrefix p i.val N (by omega) z)).1 =
      canonicalRows (perturbationOddScale p) i.val (history p N z i) ∧
    rowMap (perturbationOddScale p) i.val
      (run p i.val (experimentPrefix p i.val N (by omega) z)).1=history p N z i := by sorry
