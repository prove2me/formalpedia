-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeGeometricExecution_nativeOutput_decoded
-- name    : QEC.Coding.BDL26NativeGeometricExecution.nativeOutput_decoded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T09:42:41.225145+00:00
-- url     : https://prove2.me/theorems/5663ea68-c759-446a-9fe0-9836ed230757
-- title:
--   BDL26 Native Geometric Execution: native Output decoded
-- statement:
--   The BDL26 Native Geometric Execution construction uses the native Output decoded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricExecution.lean#L438-L446
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricExecution.lean#L438-L446

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeKeyExecutionBridge
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricExecution
import Theorems.Thm_QEC_Coding_BDL26NativeTriangleColors_nativeKey_injective

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

theorem QEC.Coding.BDL26NativeGeometricExecution.nativeOutput_decoded (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {L : ℝ} (p : GeometricParameters L)
    (T : NativeTable S n) : nativeOutput S n J p T =
      result (Presentation S n) (NC.nativeKey S n) (NC.nativeKey_injective S n)
        J p (decodedTable S n T) := by sorry
