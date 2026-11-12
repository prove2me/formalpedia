-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeGeometricAvoidance_native_dependency
-- name    : QEC.Coding.BDL26NativeGeometricAvoidance.native_dependency
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T09:05:35.804744+00:00
-- url     : https://prove2.me/theorems/360b1861-c801-4365-89c9-da40bf0203c7
-- title:
--   BDL26 Native Geometric Avoidance: native dependency
-- statement:
--   The BDL26 Native Geometric Avoidance construction uses the native dependency property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricAvoidance.lean#L44-L49
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricAvoidance.lean#L44-L49

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

theorem QEC.Coding.BDL26NativeGeometricAvoidance.native_dependency (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) (r l : ℝ) (K : ℕ)
    (ν : Vertex (Presentation S n) → Measure Space) [∀ v, IsProbabilityMeasure (ν v)] :
    HasDependencyGraph (Measure.pi ν) (localEvent (NativeSupport S n J r) (NativeBad S n J r l K))
      (supportGraph (NativeSupport S n J r)) := by sorry
