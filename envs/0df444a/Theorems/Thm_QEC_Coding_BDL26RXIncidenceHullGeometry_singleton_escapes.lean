-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXIncidenceHullGeometry_singleton_escapes
-- name    : QEC.Coding.BDL26RXIncidenceHullGeometry.singleton_escapes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T12:24:45.791766+00:00
-- url     : https://prove2.me/theorems/156ae86e-7b16-4e7e-9a59-f78c61977944
-- title:
--   BDL26 RXIncidence Hull Geometry: singleton escapes
-- statement:
--   The BDL26 RXIncidence Hull Geometry construction uses the singleton escapes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXIncidenceHullGeometry.lean#L51-L56
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXIncidenceHullGeometry.lean#L51-L56

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

theorem QEC.Coding.BDL26RXIncidenceHullGeometry.singleton_escapes (S : OddScale) {t : ℝ} (R : ℝ)
    (J : Vertex (state S (hullLevel (ballBudget t R))).presentation → Space)
    (geometry : PhysicalGeometry S (hullLevel (ballBudget t R)) J t) (center : Space) :
    ∃ q ∈ incidenceHull S (hullLevel (ballBudget t R)+1) (hullStep (ballBudget t R))
      (seed S (hullLevel (ballBudget t R))), R < dist (J (.q q)) center := by sorry
