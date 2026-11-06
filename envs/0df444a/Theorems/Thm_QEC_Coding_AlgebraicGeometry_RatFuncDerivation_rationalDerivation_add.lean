-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivation_add
-- name    : QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivation_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:14:58.438602+00:00
-- url     : https://prove2.me/theorems/24ad630b-21eb-4659-89e4-05ade621baea
-- title:
--   Rat Func Derivation: rational Derivation add
-- statement:
--   The rational derivation construction is additive in the prescribed
--   value.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/RatFuncDerivation.lean#L445-L448
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/RatFuncDerivation.lean#L445-L448

import Mathlib.RingTheory.Derivation.Basic
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_RatFuncDerivation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.RatFuncDerivation
open scoped RatFunc
variable {k M : Type*} [Field k] [AddCommGroup M] [Module k M] [Module (RatFunc k) M]
variable [IsScalarTower k (RatFunc k) M]

theorem QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivation_add (m n : M) :
    rationalDerivation (k := k) (m + n) = rationalDerivation (k := k) m
      + rationalDerivation (k := k) n := by sorry
