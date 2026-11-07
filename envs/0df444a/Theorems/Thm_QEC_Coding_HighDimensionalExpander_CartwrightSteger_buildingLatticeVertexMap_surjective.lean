-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingLatticeVertexMap_surjective
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingLatticeVertexMap_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:52:06.147732+00:00
-- url     : https://prove2.me/theorems/3cdf38d4-f811-4352-b6f4-132c35382c52
-- title:
--   Cartwright Steger: building Lattice Vertex Map surjective
-- statement:
--   The locally represented Cartwright--Steger lattice acts transitively on
--   the vertices of the rank-three or rank-four affine building.  This is the
--   orbit-surjectivity part of the Cartwright--Steger simple-transitivity
--   statement; stabilizer triviality is a separate global arithmetic claim.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingAction.lean#L1214-L1223
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingAction.lean#L1214-L1223

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Reduction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_FrobeniusCharpoly
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_BuildingAdjacency
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingAction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingLatticeVertexMap_surjective
    (P : BasePrime) (r : Rank) :
    Function.Surjective (buildingLatticeVertexMap P r) := by sorry
