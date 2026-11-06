-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncFixturePlaces_algebraMap_inverseIntegralClosureEquiv
-- name    : QEC.Coding.AlgebraicGeometry.RatFuncFixturePlaces.algebraMap_inverseIntegralClosureEquiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:49:47.591294+00:00
-- url     : https://prove2.me/theorems/98b306b6-3ba5-4f43-a500-e701eecb694b
-- title:
--   Rat Func Fixture Places: algebra Map inverse Integral Closure Equiv
-- statement:
--   The Rat Func Fixture Places construction uses the algebra Map inverse Integral Closure Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/RationalFieldPlaces.lean#L173-L206
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Places/RationalFieldPlaces.lean#L173-L206

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

theorem QEC.Coding.AlgebraicGeometry.RatFuncFixturePlaces.algebraMap_inverseIntegralClosureEquiv (p : K[X]) :
    letI : Algebra K⟮X⟯ F := InverseAffinePlace.transportedRationalAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
    letI : Algebra K[X] F := InverseAffinePlace.transportedPolynomialAlgebra (oldRationalAlgebra := oldRationalAlgebra) K F
    letI : inverseScalarTowerType := InverseAffinePlace.transportedScalarTower (oldRationalAlgebra := oldRationalAlgebra) K F
    letI : _root_.FunctionField K F := InverseAffinePlace.transportedFunctionField (oldRationalAlgebra := oldRationalAlgebra) (oldFunctionField := oldFunctionField) K F
    letI : Algebra.IsSeparable K⟮X⟯ F := InverseAffinePlace.transportedIsSeparable (oldRationalAlgebra := oldRationalAlgebra) (oldSeparable := oldSeparable) K F
    @algebraMap inverseB F _ _ inverseBToFAlgebra
        (inverseIntegralClosureEquiv p) =
      InverseAffinePlace.transportedPolynomialMap
        (oldRationalAlgebra := oldRationalAlgebra) K F p := by sorry
