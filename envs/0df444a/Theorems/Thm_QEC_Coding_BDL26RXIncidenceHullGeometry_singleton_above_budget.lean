-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXIncidenceHullGeometry_singleton_above_budget
-- name    : QEC.Coding.BDL26RXIncidenceHullGeometry.singleton_above_budget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T12:25:34.583633+00:00
-- url     : https://prove2.me/theorems/d137f9dc-b4bc-4f23-ae1b-9e20dee05e9c
-- title:
--   BDL26 RXIncidence Hull Geometry: singleton above budget
-- statement:
--   The BDL26 RXIncidence Hull Geometry construction uses the singleton above budget property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXIncidenceHullGeometry.lean#L29-L36
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXIncidenceHullGeometry.lean#L29-L36

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_QubitBallBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeFiniteComposition
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullRetainedGrowth
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullGeometry
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXIncidenceHullGeometry
open Classical MeasureTheory ProbabilityTheory
open MultiscaleDecoder BDL26IndexedDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26RandomPerturbation BDL26RandomPhysicalLocality BDL26QubitBallBounds
open BDL26RXDifferentialMasks BDL26RXIncidenceHullRetainedGrowth
open QEC.Coding.ProbabilisticConstruction.SphericalCap

theorem QEC.Coding.BDL26RXIncidenceHullGeometry.singleton_above_budget (S : OddScale) (B : Nat) :
    B < (incidenceHull S (hullLevel B+1) (hullStep B) (seed S (hullLevel B))).card := by sorry
