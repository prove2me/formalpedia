-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_differentialOrder_generator_rationalAdic
-- name    : QEC.Coding.AlgebraicGeometry.Differential.differentialOrder_generator_rationalAdic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:42:18.104207+00:00
-- url     : https://prove2.me/theorems/8f4d5746-6d89-4b0f-bdb1-2388e66a6442
-- title:
--   Differential: differential Order generator rational Adic
-- statement:
--   The actual differential generator `dX` has order zero at every finite
--   normalized rational place.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/RatFuncDifferentialOrder.lean#L164-L212
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/RatFuncDifferentialOrder.lean#L164-L212

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

theorem QEC.Coding.AlgebraicGeometry.Differential.differentialOrder_generator_rationalAdic
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) :
    differentialOrder (k := k) (F := RatFunc k)
        (GlobalPlace.rationalAdic p)
        (functionFieldDifferentialGenerator (k := k) (F := RatFunc k))
        (functionFieldDifferentialGenerator_ne_zero (k := k) (F := RatFunc k)) = 0 := by sorry
