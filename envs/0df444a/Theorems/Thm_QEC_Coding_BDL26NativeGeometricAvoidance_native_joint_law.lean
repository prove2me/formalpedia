-- Prove2me | Theorems.Thm_QEC_Coding_BDL26NativeGeometricAvoidance_native_joint_law
-- name    : QEC.Coding.BDL26NativeGeometricAvoidance.native_joint_law
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T09:04:46.845562+00:00
-- url     : https://prove2.me/theorems/a53e0a6a-d736-4126-862c-45c7654a7d65
-- title:
--   BDL26 Native Geometric Avoidance: native joint law
-- statement:
--   The BDL26 Native Geometric Avoidance construction uses the native joint law property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricAvoidance.lean#L36-L42
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/NativeGeometricAvoidance.lean#L36-L42

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

theorem QEC.Coding.BDL26NativeGeometricAvoidance.native_joint_law (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) (r : ℝ) (e : NativeEvent S n J r)
    (ν : Vertex (Presentation S n) → Measure Space) [∀ v, IsProbabilityMeasure (ν v)] :
    (Measure.pi ν).map (fun w (a : e.val) i => w (triangleVertex (Presentation S n) a.val i)) =
      Measure.pi (fun a : e.val =>
        Measure.pi (fun i => ν (triangleVertex (Presentation S n) a.val i))) := by sorry
