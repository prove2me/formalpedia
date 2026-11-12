-- Prove2me | Theorems.Thm_QEC_Coding_BDL26KeyedGeometric_keyEvent_addresses_injective
-- name    : QEC.Coding.BDL26KeyedGeometric.keyEvent_addresses_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T04:57:50.092519+00:00
-- url     : https://prove2.me/theorems/1e6bfbd1-b1af-407e-b830-dff46cf2f717
-- title:
--   BDL26 Keyed Geometric: key Event addresses injective
-- statement:
--   Four complete triangles expose twelve distinct ORIGINAL vertex addresses.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricProbability.lean#L176-L181
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricProbability.lean#L176-L181

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
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory

theorem QEC.Coding.BDL26KeyedGeometric.keyEvent_addresses_injective (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) (J : Vertex P → Space) (radius : ℝ)
    (e : KeyEvent P key hk J radius) :
    Function.Injective (fun s : (a : e.val) × Fin 3 => triangleVertex P s.1.val s.2) := by sorry
