-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_exists_rankThree_buildingGenerator_relation
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_rankThree_buildingGenerator_relation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:51:15.364192+00:00
-- url     : https://prove2.me/theorems/5e5afeed-3b04-4f91-82ac-a66b80fb9b92
-- title:
--   Cartwright Steger: exists rank Three building Generator relation
-- statement:
--   Three actual Cartwright--Steger generators trace the explicit
--   rank-three apartment loop and multiply to one in the building lattice.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/Relations.lean#L175-L185
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/Relations.lean#L175-L185

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_SimpleTransitivity
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_StrongApproximation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_Relations
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_rankThree_buildingGenerator_relation
    (P : BasePrime) :
    ∃ u0 u1 u2 : ConstantProjectiveClass P .three,
      buildingLatticeGenerator P .three u0 *
          buildingLatticeGenerator P .three u1 *
            buildingLatticeGenerator P .three u2 = 1 := by sorry
