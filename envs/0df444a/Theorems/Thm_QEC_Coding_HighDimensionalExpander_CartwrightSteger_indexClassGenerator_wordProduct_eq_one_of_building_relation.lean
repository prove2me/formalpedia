-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexClassGenerator_wordProduct_eq_one_of_building_relation
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexClassGenerator_wordProduct_eq_one_of_building_relation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:38:37.679213+00:00
-- url     : https://prove2.me/theorems/309f91bf-b907-4918-9144-4b1f96503b01
-- title:
--   Cartwright Steger: index Class Generator word Product eq one of building relation
-- statement:
--   A relation among the actual building-lattice generators remains a
--   relation after every selected finite congruence reduction.  The proof passes
--   through genuine arithmetic-order units, descends projective scalar equality
--   globally, and only then reduces coefficients.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/Relations.lean#L472-L513
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/Relations.lean#L472-L513

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_SimpleTransitivity
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_StrongApproximation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_Relations
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexClassGenerator_wordProduct_eq_one_of_building_relation
    (P : BasePrime) (r : Rank) (level : Nat)
    (word : List (ConstantProjectiveClass P r))
    (hbuilding :
      (word.map (buildingLatticeGenerator P r)).prod = 1) :
    (word.map (indexCartwrightStegerClassGenerator P r level)).prod = 1 := by sorry
