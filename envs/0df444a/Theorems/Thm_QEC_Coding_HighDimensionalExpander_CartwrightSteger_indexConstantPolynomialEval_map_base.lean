-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexConstantPolynomialEval_map_base
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexConstantPolynomialEval_map_base
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:48:59.292531+00:00
-- url     : https://prove2.me/theorems/ce25e069-f277-4fe3-a288-2b2d46215498
-- title:
--   Cartwright Steger: index Constant Polynomial Eval map base
-- statement:
--   Extending coefficients in a base-field polynomial and then evaluating is
--   the same as the original base arithmetic polynomial evaluation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Order/Reduction.lean#L78-L95
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Order/Reduction.lean#L78-L95

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Core
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexRepresentation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_Congruence
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Reduction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexConstantPolynomialEval_map_base
    (P : BasePrime) (r : Rank) (level : Nat)
    (f : PolynomialRing P) :
    indexConstantPolynomialEval P r level
        (Polynomial.map (algebraMap (BaseField P)
          (ConstantExtension P r)) f) =
      indexPolynomialEval P r level f := by sorry
