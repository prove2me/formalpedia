-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeGeometricExecution_prefix_rows
-- name    : QEC.Coding.BDL26NativeGeometricExecution.prefix_rows
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T09:41:23.601753+00:00
-- url     : https://prove2.me/theorems/16f37001-644e-44a4-9920-788665685f27
-- title:
--   BDL26 Native Geometric Execution: prefix rows
-- statement:
--   Exact counter and assignment refinement at every finite prefix.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricExecution.lean#L85-L120
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricExecution.lean#L85-L120

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

theorem QEC.Coding.BDL26NativeGeometricExecution.prefix_rows (S : OddScale) (n : ℕ) (J : Vertex (Presentation S n) → Space)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ) (T : OriginalTable S n) (m : ℕ) :
    (prefixQ S n J hr lambda K (SR.encodeSamples S n T) m).value.rows =
      SR.rowsFor (SR.indices (SR.count S n)) (SR.encodeSamples S n T)
        (fun a => counters (X := fun _ : Vertex (Presentation S n) => Space) (U S n J r) (B S n J r lambda K) T m (SR.decode S n a)) := by sorry
