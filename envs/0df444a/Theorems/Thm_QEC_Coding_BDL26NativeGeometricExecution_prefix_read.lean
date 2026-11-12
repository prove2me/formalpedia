-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeGeometricExecution_prefix_read
-- name    : QEC.Coding.BDL26NativeGeometricExecution.prefix_read
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T09:44:43.236473+00:00
-- url     : https://prove2.me/theorems/0d7a07a9-c3d3-4190-894d-e8f679b9c901
-- title:
--   BDL26 Native Geometric Execution: prefix read
-- statement:
--   The BDL26 Native Geometric Execution construction uses the prefix read property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricExecution.lean#L149-L158
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricExecution.lean#L149-L158

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeKeyExecutionBridge
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricExecution
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm

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

theorem QEC.Coding.BDL26NativeGeometricExecution.prefix_read (S : OddScale) (n : ℕ) (J : Vertex (Presentation S n) → Space)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ) (T : OriginalTable S n) (m : ℕ)
    (v : Vertex (Presentation S n)) :
    (SR.readQ ((SR.decode S n).symm v)
      (prefixQ S n J hr lambda K (SR.encodeSamples S n T) m).value.rows).value =
      (counters (X := fun _ : Vertex (Presentation S n) => Space) (U S n J r) (B S n J r lambda K) T m v,
        assignment (X := fun _ : Vertex (Presentation S n) => Space) T (counters (X := fun _ : Vertex (Presentation S n) => Space) (U S n J r) (B S n J r lambda K) T m) v) := by sorry
