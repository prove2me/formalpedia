-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_infinityCoefficientRing_inftyValuation_le_one
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.infinityCoefficientRing_inftyValuation_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:31:52.328057+00:00
-- url     : https://prove2.me/theorems/e40bc623-6e59-4ea4-997d-87eda0b4d91b
-- title:
--   Cartwright Steger: infinity Coefficient Ring infty Valuation le one
-- statement:
--   Every coefficient in the polynomial-at-infinity ring has infinity
--   valuation at most one.  This is proved directly from the adjoin
--   presentation: constants have valuation one and `1/y` has valuation
--   `exp (-1)`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityLattice.lean#L43-L73
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityLattice.lean#L43-L73

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.FieldTheory.RatFunc.Valuation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityLattice
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger._p2m_local_instance_a53544448f_18

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.infinityCoefficientRing_inftyValuation_le_one
    (P : BasePrime) (r : Rank) (a : InfinityCoefficientRing P r) :
    RatFunc.inftyValuation (ConstantExtension P r)
        (a : SplittingFunctionField P r) ≤ 1 := by sorry
