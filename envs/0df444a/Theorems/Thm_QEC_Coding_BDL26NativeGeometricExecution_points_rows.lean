-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeGeometricExecution_points_rows
-- name    : QEC.Coding.BDL26NativeGeometricExecution.points_rows
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T09:47:11.846818+00:00
-- url     : https://prove2.me/theorems/dd4cfe6f-cdeb-4c0a-bab2-9daab0a779fb
-- title:
--   BDL26 Native Geometric Execution: points rows
-- statement:
--   The BDL26 Native Geometric Execution construction uses the points rows property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricExecution.lean#L65-L73
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricExecution.lean#L65-L73

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

theorem QEC.Coding.BDL26NativeGeometricExecution.points_rows (S : OddScale) (n : ℕ) (T : OriginalTable S n)
    (c : Vertex (Presentation S n) → ℕ) :
    originalPoints S n (SR.rowsFor (SR.indices (SR.count S n)) (SR.encodeSamples S n T)
      (fun a => c (SR.decode S n a))) = assignment (X := fun _ : Vertex (Presentation S n) => Space) T c := by sorry
