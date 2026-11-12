-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeGeometricExecution_returned_original
-- name    : QEC.Coding.BDL26NativeGeometricExecution.returned_original
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T09:46:36.512563+00:00
-- url     : https://prove2.me/theorems/79f17040-806b-4874-827b-2d37bcfc73c2
-- title:
--   BDL26 Native Geometric Execution: returned original
-- statement:
--   The whole terminating output AND the original nontermination default agree.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricExecution.lean#L272-L278
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricExecution.lean#L272-L278

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

theorem QEC.Coding.BDL26NativeGeometricExecution.returned_original (S : OddScale) (n : ℕ) (J : Vertex (Presentation S n) → Space)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ) (T : OriginalTable S n) :
    returned S n J hr lambda K (SR.encodeSamples S n T) =
      output (X := fun _ : Vertex (Presentation S n) => Space) (U S n J r) (B S n J r lambda K) T := by sorry
