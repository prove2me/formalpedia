-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncFixturePlaces_xZeroAffinePlace_intValuation_imageX
-- name    : QEC.Coding.AlgebraicGeometry.RatFuncFixturePlaces.xZeroAffinePlace_intValuation_imageX
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:49:30.934051+00:00
-- url     : https://prove2.me/theorems/5d8a261f-571d-4f24-8962-4d6bf254961d
-- title:
--   Rat Func Fixture Places: x Zero Affine Place int Valuation image X
-- statement:
--   The Rat Func Fixture Places construction uses the x Zero Affine Place int Valuation image X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/RationalFieldPlaces.lean#L69-L73
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/RationalFieldPlaces.lean#L69-L73

import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.FieldTheory.RatFunc.Valuation
import Mathlib.NumberTheory.FunctionField
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Polynomial.Quotient
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffineGlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_AffinePlaceDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_InverseInfinityFibre
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RationalIntegralClosure
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_RationalFieldPlaces
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.RatFuncFixturePlaces
open scoped Polynomial RatFunc WithZero
open RatFuncFixtureDirectIntegralClosure
attribute [local instance] QEC.Coding.AlgebraicGeometry.RatFuncFixturePlaces._p2m_local_instance_59938da7a3_22
attribute [local instance] QEC.Coding.AlgebraicGeometry.RatFuncFixturePlaces.oldRationalAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.RatFuncFixturePlaces.oldPolynomialAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.RatFuncFixturePlaces.oldScalarTower
attribute [local instance] QEC.Coding.AlgebraicGeometry.RatFuncFixturePlaces.oldFunctionField
attribute [local instance] QEC.Coding.AlgebraicGeometry.RatFuncFixturePlaces.oldSeparable
attribute [local instance] QEC.Coding.AlgebraicGeometry.RatFuncFixturePlaces.oldFractionRing
attribute [local instance] QEC.Coding.AlgebraicGeometry.RatFuncFixturePlaces.directConstantAlgebra

theorem QEC.Coding.AlgebraicGeometry.RatFuncFixturePlaces.xZeroAffinePlace_intValuation_imageX :
    xZeroAffinePlace.intValuation (directIntegralClosureEquiv Polynomial.X) =
      WithZero.exp (-1 : Int) := by sorry
