-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXIncidenceHullGeometry_hullStep_even
-- name    : QEC.Coding.BDL26RXIncidenceHullGeometry.hullStep_even
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T12:25:40.916129+00:00
-- url     : https://prove2.me/theorems/a76724d6-cd39-4fe7-9c4c-fdfbef02fdf5
-- title:
--   BDL26 RXIncidence Hull Geometry: hull Step even
-- statement:
--   The BDL26 RXIncidence Hull Geometry construction uses the hull Step even property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXIncidenceHullGeometry.lean#L25-L27
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXIncidenceHullGeometry.lean#L25-L27

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

theorem QEC.Coding.BDL26RXIncidenceHullGeometry.hullStep_even (B : Nat) : (hullStep B).val % 2=0 := by sorry
