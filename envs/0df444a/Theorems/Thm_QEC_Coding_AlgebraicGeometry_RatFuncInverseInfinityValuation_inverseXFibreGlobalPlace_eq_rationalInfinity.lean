-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncInverseInfinityValuation_inverseXFibreGlobalPlace_eq_rationalInfinity
-- name    : QEC.Coding.AlgebraicGeometry.RatFuncInverseInfinityValuation.inverseXFibreGlobalPlace_eq_rationalInfinity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:07:27.394202+00:00
-- url     : https://prove2.me/theorems/19ad5616-b36b-48a2-b1be-63c5c53946ad
-- title:
--   Rat Func Inverse Infinity Valuation: inverse XFibre Global Place eq rational Infinity
-- statement:
--   The Rat Func Inverse Infinity Valuation construction uses the inverse XFibre Global Place eq rational Infinity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/RatFuncInverseInfinityValuation.lean#L200-L205
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/RatFuncInverseInfinityValuation.lean#L200-L205

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

theorem QEC.Coding.AlgebraicGeometry.RatFuncInverseInfinityValuation.inverseXFibreGlobalPlace_eq_rationalInfinity :
    inverseXFibreGlobalPlace = GlobalPlace.rationalInfinity K := by sorry
