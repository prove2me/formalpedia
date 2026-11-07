-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingLatticeVertexMap_one
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingLatticeVertexMap_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:51:31.311768+00:00
-- url     : https://prove2.me/theorems/015bfd01-be56-4cd4-a600-524cdba26173
-- title:
--   Cartwright Steger: building Lattice Vertex Map one
-- statement:
--   The Cartwright Steger construction uses the building Lattice Vertex Map one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingAction.lean#L1241-L1244
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingAction.lean#L1241-L1244

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingLatticeVertexMap_one
    (P : BasePrime) (r : Rank) :
    buildingLatticeVertexMap P r 1 = QuotientGroup.mk 1 := by sorry

attribute [defeq] QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingLatticeVertexMap_one
