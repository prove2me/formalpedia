-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncInverseInfinityValuation_inverseXFibreValuation_X_inv
-- name    : QEC.Coding.AlgebraicGeometry.RatFuncInverseInfinityValuation.inverseXFibreValuation_X_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:07:09.493783+00:00
-- url     : https://prove2.me/theorems/56229a81-16b2-4523-9932-3d44a23addd1
-- title:
--   Rat Func Inverse Infinity Valuation: inverse XFibre Valuation X inv
-- statement:
--   The Rat Func Inverse Infinity Valuation construction uses the inverse XFibre Valuation X inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/RatFuncInverseInfinityValuation.lean#L127-L153
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/RatFuncInverseInfinityValuation.lean#L127-L153

import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.FieldTheory.RatFunc.Valuation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RationalFieldPlaces
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RatFuncInverseInfinityValuation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.RatFuncInverseInfinityValuation
open scoped Polynomial RatFunc WithZero
open RatFuncFixturePlaces
attribute [local instance] QEC.Coding.AlgebraicGeometry.RatFuncInverseInfinityValuation._p2m_local_instance_de9b108ef9_13
attribute [local instance] QEC.Coding.AlgebraicGeometry.RatFuncInverseInfinityValuation.oldRationalAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.RatFuncInverseInfinityValuation.oldPolynomialAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.RatFuncInverseInfinityValuation.oldScalarTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.RatFuncInverseInfinityValuation.oldFunctionField
attribute [local instance] QEC.Coding.AlgebraicGeometry.RatFuncInverseInfinityValuation.oldSeparable
attribute [local instance] QEC.Coding.AlgebraicGeometry.RatFuncInverseInfinityValuation.oldFractionRing
attribute [local instance] QEC.Coding.AlgebraicGeometry.RatFuncInverseInfinityValuation.ratFuncDecidableEq
attribute [local instance] ratFuncDecidableEq

theorem QEC.Coding.AlgebraicGeometry.RatFuncInverseInfinityValuation.inverseXFibreValuation_X_inv :
    inverseXFibreValuation ((RatFunc.X : F)⁻¹) = WithZero.exp (-1 : Int) := by sorry
