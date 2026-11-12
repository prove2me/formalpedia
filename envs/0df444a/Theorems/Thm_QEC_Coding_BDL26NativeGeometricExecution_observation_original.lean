-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeGeometricExecution_observation_original
-- name    : QEC.Coding.BDL26NativeGeometricExecution.observation_original
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T09:51:48.391653+00:00
-- url     : https://prove2.me/theorems/36ee8705-1098-4115-bb3b-0803489ca6ad
-- title:
--   BDL26 Native Geometric Execution: observation original
-- statement:
--   The complete selected-event/counter/output/count observation, including
--   nonterminating defaults and infinity, is identified deterministically.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricExecution.lean#L340-L353
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricExecution.lean#L340-L353

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

theorem QEC.Coding.BDL26NativeGeometricExecution.observation_original (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {r : ℝ} (hr : 0 ≤ r)
    (lambda : ℝ) (K : ℕ) (T : OriginalTable S n) :
    observation S n J hr lambda K (SR.encodeSamples S n T) =
      Resampling.VariableRelabeling.jointObservation (U S n J r) (B S n J r lambda K) T := by sorry
