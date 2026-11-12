-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeGeometricExecution_full_execution_law
-- name    : QEC.Coding.BDL26NativeGeometricExecution.full_execution_law
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T10:07:42.616193+00:00
-- url     : https://prove2.me/theorems/999cc41b-45bd-4ced-aefb-0ae9b5719fde
-- title:
--   BDL26 Native Geometric Execution: full execution law
-- statement:
--   The BDL26 Native Geometric Execution construction uses the full execution law property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricExecution.lean#L415-L428
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricExecution.lean#L415-L428

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

theorem QEC.Coding.BDL26NativeGeometricExecution.full_execution_law (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {r : ℝ} (hr : 0 ≤ r)
    (lambda : ℝ) (K : ℕ) {L : ℝ} (p : GeometricParameters L) :
    (nativeTableMeasure S n p).map (observation S n J hr lambda K) =
      (tableMeasure (Presentation S n) p).map
        (Resampling.VariableRelabeling.jointObservation (U S n J r) (B S n J r lambda K)) := by sorry
