-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeGeometricExecution_native_execution_geometry_ae
-- name    : QEC.Coding.BDL26NativeGeometricExecution.native_execution_geometry_ae
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T09:45:24.925112+00:00
-- url     : https://prove2.me/theorems/d60b6485-f08c-4795-be2a-e20d8afec426
-- title:
--   BDL26 Native Geometric Execution: native execution geometry ae
-- statement:
--   The BDL26 Native Geometric Execution construction uses the native execution geometry ae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricExecution.lean#L472-L506
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricExecution.lean#L472-L506

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

theorem QEC.Coding.BDL26NativeGeometricExecution.native_execution_geometry_ae (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {L : ℝ} (p : GeometricParameters L)
    (hJ : IsBoundedDensityLocalMap (Presentation S n) J p.t) :
    Measurable (nativeOutput S n J p) ∧
    ∀ᵐ T ∂nativeTableMeasure S n p,
      NativeHalts S n J (radius_nonneg p) p.lambda ((6*p.m+2)*p.lambda) T ∧
      nativeOutput S n J p T ∈ BDL26NativeGeometricAvoidance.NativeGood S n J p ∧
      IncomingFaceGeometry (Presentation S n) (perturbationOddScale p)
        (perturbedMap (Presentation S n) J p.lambda (nativeOutput S n J p T))
        (((p.m : ℝ)-1)*p.lambda) ((6*(p.m : ℝ)*widthFactor-1)*p.lambda) ∧
      ∀ z, ((familyHits (oldTriangleImage (Presentation S n)
        (perturbedMap (Presentation S n) J p.lambda (nativeOutput S n J p T)))
        (Metric.closedBall z 1)).card : ℝ) ≤ triangleDensityBound := by sorry
