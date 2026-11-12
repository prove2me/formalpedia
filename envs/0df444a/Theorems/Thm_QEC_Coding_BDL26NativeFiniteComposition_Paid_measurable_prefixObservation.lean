-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_Paid_measurable_prefixObservation
-- name    : QEC.Coding.BDL26NativeFiniteComposition.Paid.measurable_prefixObservation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T12:23:02.116342+00:00
-- url     : https://prove2.me/theorems/2c2388c1-5d16-4d9f-acd2-2e14ae47c5c6
-- title:
--   Paid: measurable prefix Observation
-- statement:
--   Complete actual row/counter/payload/trace/cost view. Only fixed native
--   labels are discrete; every point coordinate has its original Borel structure.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeFiniteComposition.lean#L3126-L3137
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeFiniteComposition.lean#L3126-L3137

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
open QEC.Coding.BDL26NativeFiniteComposition.Paid

theorem QEC.Coding.BDL26NativeFiniteComposition.Paid.measurable_prefixObservation (S : OddScale) (n : ℕ) {r : ℝ} (hr : 0≤r)
    (lambda : ℝ) (K m : ℕ) : Measurable (fun z : JointInput S n =>
      prefixObservation S n (canonicalRows S n z.1) r lambda K z.2 m) := by sorry
