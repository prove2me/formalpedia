-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_paid_prefix_decoded
-- name    : QEC.Coding.BDL26NativeFiniteComposition.paid_prefix_decoded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T12:42:42.493518+00:00
-- url     : https://prove2.me/theorems/8414a8cb-098f-4ddc-86b7-547a1602f1dc
-- title:
--   BDL26 Native Finite Composition: paid prefix decoded
-- statement:
--   Whole paid-prefix refinement to the original decoded execution with the
--   SAME native key, retaining generated trace, every counter and every sample.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeFiniteComposition.lean#L3217-L3234
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeFiniteComposition.lean#L3217-L3234

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

theorem QEC.Coding.BDL26NativeFiniteComposition.paid_prefix_decoded (S : OddScale) (n : ℕ) (I : Rows S n)
    {r : ℝ} (hr : 0≤r) (lambda : ℝ) (K : ℕ) (T : NativeTable S n) (m : ℕ) :
    (Paid.prefixQ S n I r lambda K T m).value.1 =
      sampleRows S n T (fun a => counters (X := fun _ : Vertex (Presentation S n) => Space)
        (U S n (rowMap S n I) r) (B S n (rowMap S n I) r lambda K)
        (decodedTable S n T) m (SR.decode S n a)) ∧
    (Paid.prefixQ S n I r lambda K T m).value.2 =
      (originalTrace S n (rowMap S n I) r lambda K (decodedTable S n T) m).map
        (Option.map (originalCode S n (rowMap S n I) r)) ∧
    Paid.choice S n I r lambda K T m =
      (selected (X := fun _ : Vertex (Presentation S n) => Space)
        (U S n (rowMap S n I) r) (B S n (rowMap S n I) r lambda K)
        (decodedTable S n T) m).map (originalCode S n (rowMap S n I) r) := by sorry
