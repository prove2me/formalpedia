-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_Paid_scan_refinement
-- name    : QEC.Coding.BDL26NativeFiniteComposition.Paid.scan_refinement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T11:51:25.626897+00:00
-- url     : https://prove2.me/theorems/3db804be-50af-441b-8517-73a79363bc3e
-- title:
--   Paid: scan refinement
-- statement:
--   The Paid construction uses the scan refinement property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeFiniteComposition.lean#L457-L468
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeFiniteComposition.lean#L457-L468

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

theorem QEC.Coding.BDL26NativeFiniteComposition.Paid.scan_refinement (S : OddScale) (n : ℕ) (I : Rows S n)
    (r lambda : ℝ) (K : ℕ) (R : SR.Rows (SR.Index S n)) :
    (codeScanQ S n I r lambda K R).1 =
      (BDL26NativeGeometricJointExecution.codeScanQ S n (rowMap S n I) r lambda K R).1 ∧
    (codeScanQ S n I r lambda K R).2 ≤ multiplier I*
      (BDL26NativeGeometricJointExecution.codeScanQ S n (rowMap S n I) r lambda K R).2 := by sorry
