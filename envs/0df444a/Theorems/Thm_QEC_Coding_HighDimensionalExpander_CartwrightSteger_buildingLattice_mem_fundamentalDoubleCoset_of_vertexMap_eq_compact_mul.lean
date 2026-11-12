-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingLattice_mem_fundamentalDoubleCoset_of_vertexMap_eq_compact_mul
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingLattice_mem_fundamentalDoubleCoset_of_vertexMap_eq_compact_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:38:59.54001+00:00
-- url     : https://prove2.me/theorems/f25f8950-8dfc-4520-a5a6-634e82a66fa8
-- title:
--   Cartwright Steger: building Lattice mem fundamental Double Coset of vertex Map eq compact mul
-- statement:
--   The Cartwright Steger construction uses the building Lattice mem fundamental Double Coset of vertex Map eq compact mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/ApartmentCompletion.lean#L70-L94
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/ApartmentCompletion.lean#L70-L94

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_Relations
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_ApartmentCompletion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
open QEC.Coding.HighDimensionalExpander.SphericalHecke

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingLattice_mem_fundamentalDoubleCoset_of_vertexMap_eq_compact_mul
    (P : BasePrime) (r : Rank) (color : Nat)
    (g : BuildingCartwrightStegerLattice P r)
    (left : Matrix.ProjGenLinGroup (Fin r.matrixRank) (BuildingLocalField P))
    (hleft : left ∈ maximalCompact (BaseField P) r.matrixRank)
    (hg : buildingLatticeVertexMap P r g =
      QuotientGroup.mk
        (left * fundamentalCoweight (BaseField P) r.matrixRank color)) :
    (g : Matrix.ProjGenLinGroup (Fin r.matrixRank) (BuildingLocalField P)) ∈
      fundamentalDoubleCoset (BaseField P) r.matrixRank color := by sorry
