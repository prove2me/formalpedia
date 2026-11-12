-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingLattice_mem_fundamentalDoubleCoset_of_vertexMap_eq
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingLattice_mem_fundamentalDoubleCoset_of_vertexMap_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:20:55.355285+00:00
-- url     : https://prove2.me/theorems/2d7c44ab-328c-45d1-bacb-e66de1e63886
-- title:
--   Cartwright Steger: building Lattice mem fundamental Double Coset of vertex Map eq
-- statement:
--   The Cartwright Steger construction uses the building Lattice mem fundamental Double Coset of vertex Map eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/ApartmentCompletion.lean#L50-L68
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/ApartmentCompletion.lean#L50-L68

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_Relations
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_ApartmentCompletion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
open QEC.Coding.HighDimensionalExpander.SphericalHecke

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingLattice_mem_fundamentalDoubleCoset_of_vertexMap_eq
    (P : BasePrime) (r : Rank) (color : Nat)
    (g : BuildingCartwrightStegerLattice P r)
    (hg : buildingLatticeVertexMap P r g =
      QuotientGroup.mk
        (fundamentalCoweight (BaseField P) r.matrixRank color)) :
    (g : Matrix.ProjGenLinGroup (Fin r.matrixRank) (BuildingLocalField P)) ∈
      fundamentalDoubleCoset (BaseField P) r.matrixRank color := by sorry
