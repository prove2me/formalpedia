-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexConstantArithmeticEval_surjective
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexConstantArithmeticEval_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:50:07.142773+00:00
-- url     : https://prove2.me/theorems/ec9ff870-d75d-4573-bf8e-62286d781f4e
-- title:
--   Cartwright Steger: index Constant Arithmetic Eval surjective
-- statement:
--   Localization does not reduce the image: constant-extension polynomial
--   representatives already hit every residue-field element.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Order/Reduction.lean#L111-L118
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Order/Reduction.lean#L111-L118

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Core
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexRepresentation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_Congruence
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Reduction
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexConstantArithmeticEval_surjective
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Surjective (indexConstantArithmeticEval P r level) := by sorry
