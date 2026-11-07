-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_exists_lattice_of_colorOne_reachable
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_lattice_of_colorOne_reachable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:51:40.269505+00:00
-- url     : https://prove2.me/theorems/088ff93d-e706-4494-85d4-50ddb43fd84d
-- title:
--   Cartwright Steger: exists lattice of color One reachable
-- statement:
--   Every vertex reachable from the base by color-one building steps lies in
--   the constructed lattice orbit.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingAction.lean#L1188-L1208
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingAction.lean#L1188-L1208

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_lattice_of_colorOne_reachable
    (P : BasePrime) (r : Rank)
    (q : CartwrightStegerBuildingVertex P r)
    (hreach : Relation.ReflTransGen
      (SphericalHecke.ColoredBuildingAdjacent
        (BaseField P) r.matrixRank 1)
      (QuotientGroup.mk 1) q) :
    ∃ g : BuildingCartwrightStegerLattice P r,
      buildingLatticeVertexMap P r g = q := by sorry
