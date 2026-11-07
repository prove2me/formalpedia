-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingLatticeGenerator_adjacent_base
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingLatticeGenerator_adjacent_base
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:51:53.049202+00:00
-- url     : https://prove2.me/theorems/01cf9a9d-ecc2-43f9-8c2c-17ee35b597b3
-- title:
--   Cartwright Steger: building Lattice Generator adjacent base
-- statement:
--   Every constructed lattice generator sends the standard vertex to an
--   actual color-one adjacent building vertex.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingAction.lean#L1227-L1239
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingAction.lean#L1227-L1239

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingLatticeGenerator_adjacent_base
    (P : BasePrime) (r : Rank) (u : ConstantProjectiveClass P r) :
    SphericalHecke.ColoredBuildingAdjacent
      (BaseField P) r.matrixRank 1
      (QuotientGroup.mk 1)
      (buildingLatticeVertexMap P r (buildingLatticeGenerator P r u)) := by sorry
