-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_exists_rankFour_buildingGenerator_relation
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_rankFour_buildingGenerator_relation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:51:22.346238+00:00
-- url     : https://prove2.me/theorems/770860d2-13b7-4e24-8941-c41cef63d2ec
-- title:
--   Cartwright Steger: exists rank Four building Generator relation
-- statement:
--   Four actual Cartwright--Steger generators trace the explicit
--   rank-four apartment loop and multiply to one in the building lattice.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/Relations.lean#L386-L397
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/Relations.lean#L386-L397

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_SimpleTransitivity
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_StrongApproximation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_Relations
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_rankFour_buildingGenerator_relation
    (P : BasePrime) :
    ∃ u0 u1 u2 u3 : ConstantProjectiveClass P .four,
      ((buildingLatticeGenerator P .four u0 *
          buildingLatticeGenerator P .four u1) *
            buildingLatticeGenerator P .four u2) *
              buildingLatticeGenerator P .four u3 = 1 := by sorry
