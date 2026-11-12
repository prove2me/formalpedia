-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeGeometricExecution_prefix_trace
-- name    : QEC.Coding.BDL26NativeGeometricExecution.prefix_trace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T09:44:11.954254+00:00
-- url     : https://prove2.me/theorems/878848e5-4899-440d-92b8-274ec57f071b
-- title:
--   BDL26 Native Geometric Execution: prefix trace
-- statement:
--   The BDL26 Native Geometric Execution construction uses the prefix trace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricExecution.lean#L136-L147
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricExecution.lean#L136-L147

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

theorem QEC.Coding.BDL26NativeGeometricExecution.prefix_trace (S : OddScale) (n : ℕ) (J : Vertex (Presentation S n) → Space)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ) (T : OriginalTable S n) (m : ℕ) :
    ((prefixQ S n J hr lambda K (SR.encodeSamples S n T) m).value.trace.map
      (Option.map (event S n J r))) = originalTrace S n J r lambda K T m := by sorry
