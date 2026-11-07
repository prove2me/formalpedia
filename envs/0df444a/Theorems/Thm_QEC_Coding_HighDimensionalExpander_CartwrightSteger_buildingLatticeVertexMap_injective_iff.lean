-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingLatticeVertexMap_injective_iff
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingLatticeVertexMap_injective_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:52:35.719032+00:00
-- url     : https://prove2.me/theorems/793046e1-08ed-4df6-91ff-b5b1a2a53d0e
-- title:
--   Cartwright Steger: building Lattice Vertex Map injective iff
-- statement:
--   Injectivity of the orbit map is exactly triviality of the lattice
--   stabilizer of the standard vertex.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingAction.lean#L1259-L1283
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingAction.lean#L1259-L1283

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

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingLatticeVertexMap_injective_iff
    (P : BasePrime) (r : Rank) :
    Function.Injective (buildingLatticeVertexMap P r) ↔
      ∀ g : BuildingCartwrightStegerLattice P r,
        (g : Matrix.ProjGenLinGroup (Fin r.matrixRank)
          (BuildingLocalField P)) ∈
            SphericalHecke.maximalCompact (BaseField P) r.matrixRank →
          g = 1 := by sorry
