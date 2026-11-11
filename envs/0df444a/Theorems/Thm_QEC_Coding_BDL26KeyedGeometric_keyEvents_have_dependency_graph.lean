-- Prove2me | Theorems.Thm_QEC_Coding_BDL26KeyedGeometric_keyEvents_have_dependency_graph
-- name    : QEC.Coding.BDL26KeyedGeometric.keyEvents_have_dependency_graph
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-11T05:57:31.069207+00:00
-- url     : https://prove2.me/theorems/a18f764e-c7d8-47f9-9804-795fdc5a557c
-- title:
--   BDL26 Keyed Geometric: key Events have dependency graph
-- statement:
--   Nonneighbor independence is derived from this event's actual variable supports.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricEvents.lean#L126-L135
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/KeyedGeometricEvents.lean#L126-L135

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeTriangleColors
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Events
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricEvents
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26KeyedGeometric
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory ProbabilityTheory

theorem QEC.Coding.BDL26KeyedGeometric.keyEvents_have_dependency_graph (P : TannerSquarePresentation) (key : Triangle P → ℕ)
    (hk : Function.Injective key) (J : Vertex P → Space)
    (radius lambda : ℝ) (K : ℕ) (ν : Vertex P → Measure Space)
    [∀ v, IsProbabilityMeasure (ν v)] :
    HasDependencyGraph (Measure.pi ν)
      (localEvent (keySupport P key hk J radius) (keyBad P key hk J radius lambda K))
      (supportGraph (keySupport P key hk J radius)) := by sorry
