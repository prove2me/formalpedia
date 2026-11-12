-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeGeometricExecution_scan_rows
-- name    : QEC.Coding.BDL26NativeGeometricExecution.scan_rows
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T09:44:03.441624+00:00
-- url     : https://prove2.me/theorems/48cec616-f5fc-4ddf-9cb8-37dd2dd819e2
-- title:
--   BDL26 Native Geometric Execution: scan rows
-- statement:
--   The BDL26 Native Geometric Execution construction uses the scan rows property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricExecution.lean#L75-L82
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricExecution.lean#L75-L82

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

theorem QEC.Coding.BDL26NativeGeometricExecution.scan_rows (S : OddScale) (n : ℕ) (J : Vertex (Presentation S n) → Space)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ) (T : OriginalTable S n)
    (c : Vertex (Presentation S n) → ℕ) :
    (scanQ S n J hr lambda K
      (SR.rowsFor (SR.indices (SR.count S n)) (SR.encodeSamples S n T)
        (fun a => c (SR.decode S n a)))).1.map (event S n J r) =
      select (localEvent (X := fun _ : Vertex (Presentation S n) => Space) (U S n J r) (B S n J r lambda K)) (assignment (X := fun _ : Vertex (Presentation S n) => Space) T c) := by sorry
