-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeGeometricExecution_prefixCount_original
-- name    : QEC.Coding.BDL26NativeGeometricExecution.prefixCount_original
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T09:47:44.952196+00:00
-- url     : https://prove2.me/theorems/54b7ae7c-ab73-4991-b23e-558b5fdfd514
-- title:
--   BDL26 Native Geometric Execution: prefix Count original
-- statement:
--   The BDL26 Native Geometric Execution construction uses the prefix Count original property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricExecution.lean#L286-L291
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricExecution.lean#L286-L291

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

theorem QEC.Coding.BDL26NativeGeometricExecution.prefixCount_original (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {r : ℝ} (hr : 0 ≤ r)
    (lambda : ℝ) (K : ℕ) (T : OriginalTable S n) (m : ℕ) (e : Event S n J r) :
    nativePrefixCount S n J hr lambda K (SR.encodeSamples S n T) m e =
      prefixCount (X := fun _ : Vertex (Presentation S n) => Space) (U S n J r) (B S n J r lambda K) T m e := by sorry
