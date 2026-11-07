-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_exists_eq_algebraMap_of_constantFrobenius_eq
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_eq_algebraMap_of_constantFrobenius_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:49:34.872004+00:00
-- url     : https://prove2.me/theorems/27e6207b-52bc-4436-ae79-5896afc95ea2
-- title:
--   Cartwright Steger: exists eq algebra Map of constant Frobenius eq
-- statement:
--   The only constants fixed by arithmetic Frobenius are base-field
--   scalars.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/CyclicAlgebra.lean#L240-L256
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/CyclicAlgebra/CyclicAlgebra.lean#L240-L256

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_Arithmetic
import Mathlib.LinearAlgebra.Matrix.Notation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_CyclicAlgebra_CyclicAlgebra
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups RatFunc

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.exists_eq_algebraMap_of_constantFrobenius_eq
    (P : BasePrime) (r : Rank) (c : ConstantExtension P r)
    (hc : constantFrobenius P r c = c) :
    ∃ a : BaseField P,
      algebraMap (BaseField P) (ConstantExtension P r) a = c := by sorry
