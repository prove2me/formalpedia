-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_exists_rankFour_buildingGenerator_apartment_relation_through_neighbor
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_rankFour_buildingGenerator_apartment_relation_through_neighbor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:52:29.553893+00:00
-- url     : https://prove2.me/theorems/7620e3c3-fe2a-44db-acff-4290af943cd3
-- title:
--   Cartwright Steger: exists rank Four building Generator apartment relation through neighbor
-- statement:
--   The Cartwright Steger construction uses the exists rank Four building Generator apartment relation through neighbor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/ApartmentCompletion.lean#L504-L551
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/ApartmentCompletion.lean#L504-L551

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_Relations
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_ApartmentCompletion
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
open QEC.Coding.HighDimensionalExpander.SphericalHecke

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_rankFour_buildingGenerator_apartment_relation_through_neighbor
    (P : BasePrime) (color : Fin 3)
    (q : CartwrightStegerBuildingVertex P .four)
    (hq : q ∈ fundamentalNeighborCosets (BaseField P) 4 (color.val + 1)) :
    ∃ u0 u1 u2 u3 : ConstantProjectiveClass P .four,
      ((buildingLatticeGenerator P .four u0 *
          buildingLatticeGenerator P .four u1) *
            buildingLatticeGenerator P .four u2) *
              buildingLatticeGenerator P .four u3 = 1 ∧
      (buildingLatticeGenerator P .four u0).1 ∈
        fundamentalDoubleCoset (BaseField P) 4 1 ∧
      (buildingLatticeGenerator P .four u0 *
          buildingLatticeGenerator P .four u1).1 ∈
        fundamentalDoubleCoset (BaseField P) 4 2 ∧
      ((buildingLatticeGenerator P .four u0 *
          buildingLatticeGenerator P .four u1) *
            buildingLatticeGenerator P .four u2).1 ∈
        fundamentalDoubleCoset (BaseField P) 4 3 ∧
      buildingLatticeVertexMap P .four
        (match color.val with
        | 0 => buildingLatticeGenerator P .four u0
        | 1 => buildingLatticeGenerator P .four u0 *
            buildingLatticeGenerator P .four u1
        | _ => (buildingLatticeGenerator P .four u0 *
            buildingLatticeGenerator P .four u1) *
              buildingLatticeGenerator P .four u2) = q := by sorry
