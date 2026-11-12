-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeGeometricExecution_nonhalting_default
-- name    : QEC.Coding.BDL26NativeGeometricExecution.nonhalting_default
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T09:53:18.254038+00:00
-- url     : https://prove2.me/theorems/14402b13-9649-4705-a0f8-a8b36531e379
-- title:
--   BDL26 Native Geometric Execution: nonhalting default
-- statement:
--   The specified default is retained on every genuinely nonterminating table;
--   its total resampling count is infinite rather than the default halt clock0.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricExecution.lean#L306-L323
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricExecution.lean#L306-L323

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

theorem QEC.Coding.BDL26NativeGeometricExecution.nonhalting_default (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {r : ℝ} (hr : 0 ≤ r)
    (lambda : ℝ) (K : ℕ) (T : OriginalTable S n)
    (h : ¬ NativeHalts S n J hr lambda K (SR.encodeSamples S n T)) :
    nativeHaltTime S n J hr lambda K (SR.encodeSamples S n T) = 0 ∧
    returned S n J hr lambda K (SR.encodeSamples S n T) = (fun v => T (v,0)) ∧
    nativeTotalSteps S n J hr lambda K (SR.encodeSamples S n T) = ∞ := by sorry
