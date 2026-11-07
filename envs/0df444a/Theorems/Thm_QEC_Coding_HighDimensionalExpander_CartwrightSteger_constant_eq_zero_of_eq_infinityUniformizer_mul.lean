-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constant_eq_zero_of_eq_infinityUniformizer_mul
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.constant_eq_zero_of_eq_infinityUniformizer_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:31:50.685802+00:00
-- url     : https://prove2.me/theorems/b008306d-04f2-4223-b49d-fbe479f39afe
-- title:
--   Cartwright Steger: constant eq zero of eq infinity Uniformizer mul
-- statement:
--   A constant cannot be a nonzero multiple of the infinity uniformizer
--   inside the constructed coefficient ring.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityLattice.lean#L77-L108
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityLattice.lean#L77-L108

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.FieldTheory.RatFunc.Valuation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityLattice
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger._p2m_local_instance_a53544448f_18

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.constant_eq_zero_of_eq_infinityUniformizer_mul
    (P : BasePrime) (r : Rank) (c : ConstantExtension P r)
    (a : InfinityCoefficientRing P r)
    (h : algebraMap (ConstantExtension P r) (SplittingFunctionField P r) c =
      (infinityUniformizer P r : SplittingFunctionField P r) *
        (a : SplittingFunctionField P r)) :
    c = 0 := by sorry
