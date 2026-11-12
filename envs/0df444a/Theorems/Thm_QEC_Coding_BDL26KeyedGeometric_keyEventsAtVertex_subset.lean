-- Prove2me | Theorems.Thm_QEC_Coding_BDL26KeyedGeometric_keyEventsAtVertex_subset
-- name    : QEC.Coding.BDL26KeyedGeometric.keyEventsAtVertex_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T06:00:28.534809+00:00
-- url     : https://prove2.me/theorems/1908dfd8-bc53-4a0c-983a-5b5ffe539125
-- title:
--   BDL26 Keyed Geometric: key Events At Vertex subset
-- statement:
--   The BDL26 Keyed Geometric construction uses the key Events At Vertex subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricCounts.lean#L54-L64
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricCounts.lean#L54-L64

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

theorem QEC.Coding.BDL26KeyedGeometric.keyEventsAtVertex_subset (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) (J : Vertex P → Space)
    (K : ℕ) (v : Vertex P) :
    keyEventsAtVertex P key hk J K v ⊆ (incidentTriangles P v).biUnion (keyEventsAtTriangle P key hk J K) := by sorry
