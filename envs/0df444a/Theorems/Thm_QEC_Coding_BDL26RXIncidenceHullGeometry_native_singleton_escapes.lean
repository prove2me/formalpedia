-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXIncidenceHullGeometry_native_singleton_escapes
-- name    : QEC.Coding.BDL26RXIncidenceHullGeometry.native_singleton_escapes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T12:06:22.059345+00:00
-- url     : https://prove2.me/theorems/dd74337d-605b-41ec-af26-126b5dd3bfb3
-- title:
--   BDL26 RXIncidence Hull Geometry: native singleton escapes
-- statement:
--   Every successful original native history has this same singleton escape.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXIncidenceHullGeometry.lean#L59-L69
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXIncidenceHullGeometry.lean#L59-L69

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

theorem QEC.Coding.BDL26RXIncidenceHullGeometry.native_singleton_escapes {L : ℝ} (p : GeometricParameters L) (R : ℝ)
    {z : BDL26NativeFiniteComposition.Experiment p (hullLevel (ballBudget p.t R)+1)}
    (success : z ∈ BDL26NativeFiniteComposition.finiteSuccess p (hullLevel (ballBudget p.t R)+1))
    (center : Space) :
    ∃ q ∈ incidenceHull (perturbationOddScale p) (hullLevel (ballBudget p.t R)+1)
      (hullStep (ballBudget p.t R)) (seed (perturbationOddScale p) (hullLevel (ballBudget p.t R))),
      R < dist (BDL26NativeFiniteComposition.history p (hullLevel (ballBudget p.t R)+1) z
        ⟨hullLevel (ballBudget p.t R),by omega⟩ (.q q)) center := by sorry
