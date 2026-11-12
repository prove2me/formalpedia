-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeGeometricExecution_observation_decoded
-- name    : QEC.Coding.BDL26NativeGeometricExecution.observation_decoded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T09:43:36.070906+00:00
-- url     : https://prove2.me/theorems/5b4557bb-024f-494e-a86e-f477f5b692e3
-- title:
--   BDL26 Native Geometric Execution: observation decoded
-- statement:
--   The BDL26 Native Geometric Execution construction uses the observation decoded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricExecution.lean#L362-L370
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricExecution.lean#L362-L370

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

theorem QEC.Coding.BDL26NativeGeometricExecution.observation_decoded (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {r : ℝ} (hr : 0 ≤ r)
    (lambda : ℝ) (K : ℕ) (T : NativeTable S n) :
    observation S n J hr lambda K T =
      Resampling.VariableRelabeling.jointObservation (U S n J r) (B S n J r lambda K)
        (decodedTable S n T) := by sorry
