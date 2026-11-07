-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingLatticeVertexMap_eq_iff
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingLatticeVertexMap_eq_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:52:06.429192+00:00
-- url     : https://prove2.me/theorems/eaa119c4-459c-42c7-bbac-931630183253
-- title:
--   Cartwright Steger: building Lattice Vertex Map eq iff
-- statement:
--   The Cartwright Steger construction uses the building Lattice Vertex Map eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingAction.lean#L1246-L1255
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingAction.lean#L1246-L1255

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingLatticeVertexMap_eq_iff
    (P : BasePrime) (r : Rank)
    (g h : BuildingCartwrightStegerLattice P r) :
    buildingLatticeVertexMap P r g = buildingLatticeVertexMap P r h ↔
      ((g : Matrix.ProjGenLinGroup (Fin r.matrixRank)
          (BuildingLocalField P))⁻¹ *
        (h : Matrix.ProjGenLinGroup (Fin r.matrixRank)
          (BuildingLocalField P))) ∈
        SphericalHecke.maximalCompact (BaseField P) r.matrixRank := by sorry
