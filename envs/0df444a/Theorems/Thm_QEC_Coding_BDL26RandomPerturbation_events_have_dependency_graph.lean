-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_events_have_dependency_graph
-- name    : QEC.Coding.BDL26RandomPerturbation.events_have_dependency_graph
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T21:56:46.355044+00:00
-- url     : https://prove2.me/theorems/f9b6fcdf-9a10-4545-9d37-08dcc9946c17
-- title:
--   BDL26 Random Perturbation: events have dependency graph
-- statement:
--   Nonneighbor independence is derived from this event's actual variable supports.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/Events.lean#L118-L126
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RandomPerturbation/Events.lean#L118-L126

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_IncomingGeometry
import Mathlib.Data.Nat.Choose.Bounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Events
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory

theorem QEC.Coding.BDL26RandomPerturbation.events_have_dependency_graph (P : TannerSquarePresentation) (J : Vertex P → Space)
    (radius lambda : ℝ) (K : ℕ) (ν : Vertex P → Measure Space)
    [∀ v, IsProbabilityMeasure (ν v)] :
    HasDependencyGraph (Measure.pi ν)
      (localEvent (eventSupport P J radius) (eventBad P J radius lambda K))
      (supportGraph (eventSupport P J radius)) := by sorry
