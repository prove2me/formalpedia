-- Prove2me | Theorems.Thm_QEC_Coding_BDL26KeyedGeometric_key_triangle_hit_probability
-- name    : QEC.Coding.BDL26KeyedGeometric.key_triangle_hit_probability
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T05:58:08.531219+00:00
-- url     : https://prove2.me/theorems/37f0456b-0c58-43e4-b481-5348b7b52bca
-- title:
--   BDL26 Keyed Geometric: key triangle hit probability
-- statement:
--   A fixed ball is tested against every selected triangle; no pairwise-only shortcut.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricProbability.lean#L59-L86
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricProbability.lean#L59-L86

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

theorem QEC.Coding.BDL26KeyedGeometric.key_triangle_hit_probability (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key)
    {A : Type*} [Fintype A] (labels : A → Triangle P) (hinj : Function.Injective labels)
    (hcolor : ∀ a b, BDL26NativeTriangleColors.policyColor P key (labels a) = BDL26NativeTriangleColors.policyColor P key (labels b))
    {R c ρ : ℝ} (hR : 0 < R) (hc0 : -1 < c) (hc1 : c < 1) (hρ : 0 ≤ ρ)
    (J : Vertex P → Space) (z : Space) :
    Measure.pi (vertexLaw P R c)
      {p | ∀ a, (fun i => p (triangleVertex P (labels a) i)) ∈
        triangleHit (fun i => J (triangleVertex P (labels a) i)) z ρ} ≤
      ENNReal.ofReal (18*ρ/(R*(1-c))) ^ Fintype.card A := by sorry
