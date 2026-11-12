-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeGeometricExecution_native_expected_steps
-- name    : QEC.Coding.BDL26NativeGeometricExecution.native_expected_steps
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T09:53:07.384529+00:00
-- url     : https://prove2.me/theorems/c66c45d9-8f73-4d0c-9fe7-8fcaea786867
-- title:
--   BDL26 Native Geometric Execution: native expected steps
-- statement:
--   Explicit finite expected totalSteps for the same paid native selection process.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricExecution.lean#L509-L538
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricExecution.lean#L509-L538

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

theorem QEC.Coding.BDL26NativeGeometricExecution.native_expected_steps (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {L : ℝ} (p : GeometricParameters L)
    (hJ : IsBoundedDensityLocalMap (Presentation S n) J p.t) :
    (∫⁻ T, nativeTotalSteps S n J (radius_nonneg p) p.lambda ((6*p.m+2)*p.lambda) T
      ∂nativeTableMeasure S n p) ≤
      ENNReal.ofReal ((Fintype.card (Triangle (Presentation S n)) : ℝ)^4 *
        (lllWeight (dependencyBound p.M)/(1-lllWeight (dependencyBound p.M)))) ∧
    ENNReal.ofReal ((Fintype.card (Triangle (Presentation S n)) : ℝ)^4 *
        (lllWeight (dependencyBound p.M)/(1-lllWeight (dependencyBound p.M)))) < ∞ := by sorry
