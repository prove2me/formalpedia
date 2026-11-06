-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
-- name    : QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:14:10.813848+00:00
-- url     : https://prove2.me/theorems/a6dd31cf-98c1-4757-a1e6-d6ce585c9992
-- title:
--   Rat Func Derivation: rational Derivation Equiv symm apply
-- statement:
--   The Rat Func Derivation construction uses the rational Derivation Equiv symm apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/RatFuncDerivation.lean#L434-L436
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/RatFuncDerivation.lean#L434-L436

import Mathlib.RingTheory.Derivation.Basic
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_RatFuncDerivation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.RatFuncDerivation
open scoped RatFunc
variable {k M : Type*} [Field k] [AddCommGroup M] [Module k M] [Module (RatFunc k) M]
variable [IsScalarTower k (RatFunc k) M]

theorem QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply (m : M) :
    (rationalDerivationEquiv (k := k) (M := M)).symm m = rationalDerivation (k := k) m := by sorry

attribute [defeq] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply
