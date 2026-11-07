-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexConstantPolynomialEval_surjective
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexConstantPolynomialEval_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:49:07.622979+00:00
-- url     : https://prove2.me/theorems/96687305-da9c-4649-b4a1-f5a5d2b1cf6c
-- title:
--   Cartwright Steger: index Constant Polynomial Eval surjective
-- statement:
--   The constant-extended polynomial evaluation remains onto, since its
--   base-field polynomial subring already reaches the full selected residue
--   field.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Order/Reduction.lean#L100-L107
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Order/Reduction.lean#L100-L107

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Core
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexRepresentation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_Congruence
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Reduction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexConstantPolynomialEval_surjective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Surjective (indexConstantPolynomialEval P r level) := by sorry
