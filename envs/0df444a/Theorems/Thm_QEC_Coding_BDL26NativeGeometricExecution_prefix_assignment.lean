-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeGeometricExecution_prefix_assignment
-- name    : QEC.Coding.BDL26NativeGeometricExecution.prefix_assignment
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T09:45:33.002207+00:00
-- url     : https://prove2.me/theorems/10c83e90-9007-4bcf-9ab3-6f14cd850072
-- title:
--   BDL26 Native Geometric Execution: prefix assignment
-- statement:
--   The BDL26 Native Geometric Execution construction uses the prefix assignment property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricExecution.lean#L160-L164
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricExecution.lean#L160-L164

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

theorem QEC.Coding.BDL26NativeGeometricExecution.prefix_assignment (S : OddScale) (n : ℕ) (J : Vertex (Presentation S n) → Space)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ) (T : OriginalTable S n) (m : ℕ) :
    originalPoints S n (prefixQ S n J hr lambda K (SR.encodeSamples S n T) m).value.rows =
      assignment (X := fun _ : Vertex (Presentation S n) => Space) T (counters (X := fun _ : Vertex (Presentation S n) => Space) (U S n J r) (B S n J r lambda K) T m) := by sorry
