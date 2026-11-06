-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_differentialOrder_smul_generator_rationalInfinity
-- name    : QEC.Coding.AlgebraicGeometry.Differential.differentialOrder_smul_generator_rationalInfinity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:42:01.420124+00:00
-- url     : https://prove2.me/theorems/3fed9ddf-ce5e-4b01-b197-322b62a5f55c
-- title:
--   Differential: differential Order smul generator rational Infinity
-- statement:
--   Scaling `dX` by a nonzero rational function gives the function order minus
--   two at the normalized rational place at infinity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/RatFuncDifferentialOrder.lean#L295-L321
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/RatFuncDifferentialOrder.lean#L295-L321

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

theorem QEC.Coding.AlgebraicGeometry.Differential.differentialOrder_smul_generator_rationalInfinity
    (f : RatFunc k) (hf : f ≠ 0) :
    differentialOrder (k := k) (F := RatFunc k)
        (GlobalPlace.rationalInfinity k)
        (f • functionFieldDifferentialGenerator (k := k) (F := RatFunc k))
        (smul_ne_zero hf
          (functionFieldDifferentialGenerator_ne_zero (k := k) (F := RatFunc k))) =
      (GlobalPlace.rationalInfinity k).order f - 2 := by sorry
