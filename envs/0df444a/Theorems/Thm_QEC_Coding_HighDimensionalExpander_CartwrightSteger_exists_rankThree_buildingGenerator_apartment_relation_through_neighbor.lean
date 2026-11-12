-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_exists_rankThree_buildingGenerator_apartment_relation_through_neighbor
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_rankThree_buildingGenerator_apartment_relation_through_neighbor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:51:46.584925+00:00
-- url     : https://prove2.me/theorems/7740cbb2-daf1-4598-925e-7d82f494473c
-- title:
--   Cartwright Steger: exists rank Three building Generator apartment relation through neighbor
-- statement:
--   The Cartwright Steger construction uses the exists rank Three building Generator apartment relation through neighbor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/ApartmentCompletion.lean#L254-L286
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/ApartmentCompletion.lean#L254-L286

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_Relations
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_ApartmentCompletion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
open QEC.Coding.HighDimensionalExpander.SphericalHecke

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_rankThree_buildingGenerator_apartment_relation_through_neighbor
    (P : BasePrime) (color : Fin 2)
    (q : CartwrightStegerBuildingVertex P .three)
    (hq : q ∈ fundamentalNeighborCosets (BaseField P) 3 (color.val + 1)) :
    ∃ u0 u1 u2 : ConstantProjectiveClass P .three,
      buildingLatticeGenerator P .three u0 *
          buildingLatticeGenerator P .three u1 *
            buildingLatticeGenerator P .three u2 = 1 ∧
      (buildingLatticeGenerator P .three u0).1 ∈
        fundamentalDoubleCoset (BaseField P) 3 1 ∧
      (buildingLatticeGenerator P .three u0 *
          buildingLatticeGenerator P .three u1).1 ∈
        fundamentalDoubleCoset (BaseField P) 3 2 ∧
      buildingLatticeVertexMap P .three
        (if color = 0 then buildingLatticeGenerator P .three u0
          else buildingLatticeGenerator P .three u0 *
            buildingLatticeGenerator P .three u1) = q := by sorry
