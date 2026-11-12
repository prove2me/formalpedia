-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeGeometricAvoidance_native_criterion
-- name    : QEC.Coding.BDL26NativeGeometricAvoidance.native_criterion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T09:05:00.887031+00:00
-- url     : https://prove2.me/theorems/419e3ba0-eced-46ab-8881-fdc3e531545e
-- title:
--   BDL26 Native Geometric Avoidance: native criterion
-- statement:
--   The BDL26 Native Geometric Avoidance construction uses the native criterion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricAvoidance.lean#L69-L80
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricAvoidance.lean#L69-L80

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

theorem QEC.Coding.BDL26NativeGeometricAvoidance.native_criterion (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {L : ℝ} (p : GeometricParameters L)
    (hJ : IsBoundedDensityLocalMap (Presentation S n) J p.t)
    (e : NativeEvent S n J (anchorRadius p.m)) :
    (geometricLaw (Presentation S n) p).real
      (localEvent (NativeSupport S n J (anchorRadius p.m))
        (NativeBad S n J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) e) ≤
      lllWeight (dependencyBound p.M) *
        ∏ _f ∈ (supportGraph (NativeSupport S n J (anchorRadius p.m))).neighborFinset e,
          (1-lllWeight (dependencyBound p.M)) := by sorry
