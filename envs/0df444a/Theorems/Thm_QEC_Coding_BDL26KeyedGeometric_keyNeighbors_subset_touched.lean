-- Prove2me | Theorems.Thm_QEC_Coding_BDL26KeyedGeometric_keyNeighbors_subset_touched
-- name    : QEC.Coding.BDL26KeyedGeometric.keyNeighbors_subset_touched
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T06:01:47.297837+00:00
-- url     : https://prove2.me/theorems/0dccc20e-a352-4f74-8492-85852e287651
-- title:
--   BDL26 Keyed Geometric: key Neighbors subset touched
-- statement:
--   Every actual graph neighbor touches one of the event's actual support vertices.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricCounts.lean#L83-L94
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricCounts.lean#L83-L94

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricEvents
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_DependencyCounts
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricCounts
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26KeyedGeometric
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory ProbabilityTheory

theorem QEC.Coding.BDL26KeyedGeometric.keyNeighbors_subset_touched (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) (J : Vertex P → Space)
    (K : ℕ) (e : KeyEvent P key hk J K) :
    (supportGraph (keySupport P key hk J K)).neighborFinset e ⊆
      (keySupport P key hk J K e).biUnion (keyEventsAtVertex P key hk J K) := by sorry
