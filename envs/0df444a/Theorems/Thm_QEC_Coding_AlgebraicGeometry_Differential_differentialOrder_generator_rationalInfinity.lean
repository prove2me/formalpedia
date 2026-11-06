-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_differentialOrder_generator_rationalInfinity
-- name    : QEC.Coding.AlgebraicGeometry.Differential.differentialOrder_generator_rationalInfinity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:41:48.759659+00:00
-- url     : https://prove2.me/theorems/28459df4-9080-42dc-ad2a-984622813b08
-- title:
--   Differential: differential Order generator rational Infinity
-- statement:
--   The actual differential generator `dX` has order `-2` at the normalized
--   rational place at infinity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/RatFuncDifferentialOrder.lean#L216-L262
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/RatFuncDifferentialOrder.lean#L216-L262

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicSimpleFractionResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_InfinitySimpleFractionResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_RatFuncDifferentialOrder
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_functionFieldDifferentialGenerator_ne_zero

set_option autoImplicit false
open scoped Polynomial RatFunc WithZero
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.Differential
open FunctionFieldDifferential
variable {k : Type*} [Field k] [Finite k]

theorem QEC.Coding.AlgebraicGeometry.Differential.differentialOrder_generator_rationalInfinity :
    differentialOrder (k := k) (F := RatFunc k)
        (GlobalPlace.rationalInfinity k)
        (functionFieldDifferentialGenerator (k := k) (F := RatFunc k))
        (functionFieldDifferentialGenerator_ne_zero (k := k) (F := RatFunc k)) = -2 := by sorry
