-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
-- name    : QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:13:53.674005+00:00
-- url     : https://prove2.me/theorems/63f74a45-f639-45ad-8368-fd141b935d02
-- title:
--   Rat Func Derivation: rational Derivation Equiv apply
-- statement:
--   The Rat Func Derivation construction uses the rational Derivation Equiv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/RatFuncDerivation.lean#L429-L431
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Differentials/RatFuncDerivation.lean#L429-L431

import Mathlib.RingTheory.Derivation.Basic
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_RatFuncDerivation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.RatFuncDerivation
open scoped RatFunc
variable {k M : Type*} [Field k] [AddCommGroup M] [Module k M] [Module (RatFunc k) M]
variable [IsScalarTower k (RatFunc k) M]

theorem QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply (D : Derivation k (RatFunc k) M) :
    rationalDerivationEquiv (k := k) (M := M) D = D RatFunc.X := by sorry

attribute [defeq] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
