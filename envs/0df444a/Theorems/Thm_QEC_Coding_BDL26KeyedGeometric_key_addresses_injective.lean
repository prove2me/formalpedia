-- Prove2me | Theorems.Thm_QEC_Coding_BDL26KeyedGeometric_key_addresses_injective
-- name    : QEC.Coding.BDL26KeyedGeometric.key_addresses_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T04:56:47.5241+00:00
-- url     : https://prove2.me/theorems/0ed6e8d4-7623-45f0-bffc-deba90c03289
-- title:
--   BDL26 Keyed Geometric: key addresses injective
-- statement:
--   Joint address injectivity follows from the proved incidence-rank coloring.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricProbability.lean#L17-L31
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricProbability.lean#L17-L31

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

theorem QEC.Coding.BDL26KeyedGeometric.key_addresses_injective (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key)
    {A : Type*} (labels : A → Triangle P) (hinj : Function.Injective labels)
    (hcolor : ∀ a b, BDL26NativeTriangleColors.policyColor P key (labels a) = BDL26NativeTriangleColors.policyColor P key (labels b)) :
    Function.Injective (fun s : (a : A) × Fin 3 => triangleVertex P (labels s.1) s.2) := by sorry
