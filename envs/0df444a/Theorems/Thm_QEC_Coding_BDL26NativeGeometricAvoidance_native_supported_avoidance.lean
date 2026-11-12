-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeGeometricAvoidance_native_supported_avoidance
-- name    : QEC.Coding.BDL26NativeGeometricAvoidance.native_supported_avoidance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T06:04:39.540572+00:00
-- url     : https://prove2.me/theorems/e55af159-fc95-4cd6-938f-5e2fe8c9f6ea
-- title:
--   BDL26 Native Geometric Avoidance: native supported avoidance
-- statement:
--   Every level, parity, copy and odd scale is retained; no caller key/valence/probability witness.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricAvoidance.lean#L83-L97
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricAvoidance.lean#L83-L97

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricLegacy
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricAvoidance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativeGeometricAvoidance
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding
open BDL26FiniteAlternatingCore BDL26TannerLocalRegularity BDL26RandomPerturbation
open BDL26KeyedGeometric
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory

theorem QEC.Coding.BDL26NativeGeometricAvoidance.native_supported_avoidance (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {L : ℝ} (p : GeometricParameters L)
    (hJ : IsBoundedDensityLocalMap (Presentation S n) J p.t) :
    MeasurableSet (NativeGood S n J p) ∧
    0 < (geometricLaw (Presentation S n) p).real (NativeGood S n J p) ∧
    ∀ w ∈ NativeGood S n J p,
      IncomingFaceGeometry (Presentation S n) (perturbationOddScale p)
        (perturbedMap (Presentation S n) J p.lambda w)
        (((p.m : ℝ)-1)*p.lambda) ((6*(p.m : ℝ)*widthFactor-1)*p.lambda) ∧
      ∀ z, ((familyHits (oldTriangleImage (Presentation S n)
        (perturbedMap (Presentation S n) J p.lambda w))
        (Metric.closedBall z 1)).card : ℝ) ≤ triangleDensityBound := by sorry
