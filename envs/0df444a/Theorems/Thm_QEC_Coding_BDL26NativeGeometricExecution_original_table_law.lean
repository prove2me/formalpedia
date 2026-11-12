-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeGeometricExecution_original_table_law
-- name    : QEC.Coding.BDL26NativeGeometricExecution.original_table_law
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T10:07:41.6012+00:00
-- url     : https://prove2.me/theorems/0f6377e3-081e-4d04-9054-744f1180f24f
-- title:
--   BDL26 Native Geometric Execution: original table law
-- statement:
--   The genuine original product law is transported through the generated decode equivalence.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricExecution.lean#L392-L396
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricExecution.lean#L392-L396

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeKeyExecutionBridge
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricExecution
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26NativeGeometricExecution
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26BoundedValence
open BDL26ReplacementEmbedding BDL26TannerLocalRegularity
open BDL26RandomPerturbation BDL26KeyedGeometric BDL26KeyedGeometricExecution
open BDL26NativeKeyExecutionBridge
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
open scoped Classical BigOperators ENNReal

theorem QEC.Coding.BDL26NativeGeometricExecution.original_table_law (S : OddScale) (n : ℕ) {L : ℝ} (p : GeometricParameters L) :
    (tableMeasure (Presentation S n) p).map (SR.encodeSamples S n) = nativeTableMeasure S n p := by sorry
