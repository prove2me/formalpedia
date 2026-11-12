-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXIncidenceHullGeometry_large_mask_escapes
-- name    : QEC.Coding.BDL26RXIncidenceHullGeometry.large_mask_escapes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T12:25:37.248588+00:00
-- url     : https://prove2.me/theorems/266cb5e9-f914-4ace-b3cd-efc664da35d3
-- title:
--   BDL26 RXIncidence Hull Geometry: large mask escapes
-- statement:
--   Cardinality becomes a spatial escape only after applying actual density.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXIncidenceHullGeometry.lean#L39-L49
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/OwnerIncidenceMasks/RXIncidenceHullGeometry.lean#L39-L49

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

theorem QEC.Coding.BDL26RXIncidenceHullGeometry.large_mask_escapes (S : OddScale) (m : Nat)
    (J : Vertex (state S m).presentation → Space) {t : ℝ}
    (geometry : PhysicalGeometry S m J t) (R : ℝ)
    (A : Finset (state S m).presentation.Q) (heavy : ballBudget t R < A.card)
    (center : Space) : ∃ q ∈ A, R < dist (J (.q q)) center := by sorry
