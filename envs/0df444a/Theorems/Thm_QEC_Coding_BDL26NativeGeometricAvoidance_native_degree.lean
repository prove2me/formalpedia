-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeGeometricAvoidance_native_degree
-- name    : QEC.Coding.BDL26NativeGeometricAvoidance.native_degree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T09:03:37.661341+00:00
-- url     : https://prove2.me/theorems/bf408e46-3efa-4cd7-9076-9c7346c9c529
-- title:
--   BDL26 Native Geometric Avoidance: native degree
-- statement:
--   The BDL26 Native Geometric Avoidance construction uses the native degree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricAvoidance.lean#L60-L67
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricAvoidance.lean#L60-L67

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

theorem QEC.Coding.BDL26NativeGeometricAvoidance.native_degree (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) {L : ℝ} (p : GeometricParameters L)
    (hJ : IsBoundedDensityLocalMap (Presentation S n) J p.t)
    (e : NativeEvent S n J (anchorRadius p.m)) :
    ((supportGraph (NativeSupport S n J (anchorRadius p.m))).neighborFinset e).card ≤
      dependencyBound p.M := by sorry
