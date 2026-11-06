-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivation_smul
-- name    : QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivation_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:14:45.981677+00:00
-- url     : https://prove2.me/theorems/6669a7f0-c783-4f26-aa69-9c2179ac2afb
-- title:
--   Rat Func Derivation: rational Derivation smul
-- statement:
--   The rational derivation construction is linear in the prescribed value.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/RatFuncDerivation.lean#L439-L441
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/RatFuncDerivation.lean#L439-L441

import Mathlib.RingTheory.Derivation.Basic
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_RatFuncDerivation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.RatFuncDerivation
open scoped RatFunc
variable {k M : Type*} [Field k] [AddCommGroup M] [Module k M] [Module (RatFunc k) M]
variable [IsScalarTower k (RatFunc k) M]

theorem QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivation_smul (a : RatFunc k) (m : M) :
    rationalDerivation (k := k) (a • m) = a • rationalDerivation (k := k) m := by sorry
