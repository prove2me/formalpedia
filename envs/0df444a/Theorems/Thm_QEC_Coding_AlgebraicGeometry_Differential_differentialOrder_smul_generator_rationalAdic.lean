-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_differentialOrder_smul_generator_rationalAdic
-- name    : QEC.Coding.AlgebraicGeometry.Differential.differentialOrder_smul_generator_rationalAdic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:41:52.190761+00:00
-- url     : https://prove2.me/theorems/67ba24d2-cdba-4329-899b-bf6236c7bc18
-- title:
--   Differential: differential Order smul generator rational Adic
-- statement:
--   Scaling `dX` by a nonzero rational function gives exactly the function's
--   order at a finite rational place.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/RatFuncDifferentialOrder.lean#L266-L291
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/RatFuncDifferentialOrder.lean#L266-L291

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

theorem QEC.Coding.AlgebraicGeometry.Differential.differentialOrder_smul_generator_rationalAdic
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) (f : RatFunc k) (hf : f ≠ 0) :
    differentialOrder (k := k) (F := RatFunc k)
        (GlobalPlace.rationalAdic p)
        (f • functionFieldDifferentialGenerator (k := k) (F := RatFunc k))
        (smul_ne_zero hf
          (functionFieldDifferentialGenerator_ne_zero (k := k) (F := RatFunc k))) =
      (GlobalPlace.rationalAdic p).order f := by sorry
