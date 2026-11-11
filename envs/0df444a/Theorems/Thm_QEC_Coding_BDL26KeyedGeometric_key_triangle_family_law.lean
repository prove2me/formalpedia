-- Prove2me | Theorems.Thm_QEC_Coding_BDL26KeyedGeometric_key_triangle_family_law
-- name    : QEC.Coding.BDL26KeyedGeometric.key_triangle_family_law
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T04:57:21.121472+00:00
-- url     : https://prove2.me/theorems/80d9c08b-203c-4cf0-bc88-3bf9cce2e04b
-- title:
--   BDL26 Keyed Geometric: key triangle family law
-- statement:
--   Reindexing the actual vertex product derives a joint product of triangle laws.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricProbability.lean#L34-L56
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricProbability.lean#L34-L56

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricEvents
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ProbabilityDecay
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ConcreteParameters
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26KeyedGeometric
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory ProbabilityTheory

theorem QEC.Coding.BDL26KeyedGeometric.key_triangle_family_law (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) {A : Type*} [Fintype A]
    (labels : A → Triangle P) (hinj : Function.Injective labels)
    (hcolor : ∀ a b, BDL26NativeTriangleColors.policyColor P key (labels a) = BDL26NativeTriangleColors.policyColor P key (labels b))
    (ν : Vertex P → Measure Space) [∀ v, IsProbabilityMeasure (ν v)] :
    (Measure.pi ν).map (fun p a i => p (triangleVertex P (labels a) i)) =
      Measure.pi (fun a => Measure.pi (fun i => ν (triangleVertex P (labels a) i))) := by sorry
