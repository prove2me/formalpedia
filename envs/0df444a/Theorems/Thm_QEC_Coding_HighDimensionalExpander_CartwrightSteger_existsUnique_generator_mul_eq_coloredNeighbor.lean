-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_existsUnique_generator_mul_eq_coloredNeighbor
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.existsUnique_generator_mul_eq_coloredNeighbor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:51:49.661425+00:00
-- url     : https://prove2.me/theorems/5f38f028-e774-4b4f-98d6-2179e6be953a
-- title:
--   Cartwright Steger: exists Unique generator mul eq colored Neighbor
-- statement:
--   Every color-one neighbor of a lattice-orbit vertex is reached by a
--   unique source generator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingAction.lean#L1157-L1184
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingAction.lean#L1157-L1184

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.existsUnique_generator_mul_eq_coloredNeighbor
    (P : BasePrime) (r : Rank)
    (g : BuildingCartwrightStegerLattice P r)
    (q : CartwrightStegerBuildingVertex P r)
    (hq : SphericalHecke.ColoredBuildingAdjacent
      (BaseField P) r.matrixRank 1
      (buildingLatticeVertexMap P r g) q) :
    ∃! u : ConstantProjectiveClass P r,
      buildingLatticeVertexMap P r
        (g * buildingLatticeGenerator P r u) = q := by sorry
